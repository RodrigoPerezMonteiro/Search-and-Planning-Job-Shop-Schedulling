;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                                                                       ;

;                            PPlan | MEIC-A                             ;

;                              Grupo XX                                 ;

;                      DIOGO COSTA      | 72770                         ;

;                      RODRIGO MONTEIRO | 73701                         ;

;                         Job-shop scheduling                           ;

;                                                                       ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package :user)

;(compile-file "procura.lisp")

;(load "procura")


(defvar *RESULT*)
(defvar *ALL-GEN-STATES* )

(setq *RESULT* nil)
(setq *ALL-GEN-STATES* (list))

;; Limite de tempo para execução
(defconstant MAX-SECONDS 270)
(defvar MAX-DEPTH 0)
(defvar *EXPANDED* 0)
(defvar *GENERATED* 0)


(declaim 

	(optimize 

			(speed 3)

			(space 3)

			(compilation-speed 3)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;               		States Declaration/Creation                 	;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defstruct 	state
			jobs-lst
			n.jobs
			n.machines
			precedence-solved
			heuristic-eval
			discrepancy
			explorado?
)

;Inicia o problema sem violacoes da restricao de precedencia
(defun setup-init-state (state)

	(progn
		(loop for job in (state-jobs-lst state) do
			(loop for taskA in (job-shop-job-tasks job)  
				  for taskB in (cdr (job-shop-job-tasks job))

				do (progn 
					(if (eql taskA (car (job-shop-job-tasks job)))
						(setf (job-shop-task-start.time taskA) 0)
						)

					(setf (job-shop-task-start.time taskB) (+ (job-shop-task-start.time taskA)
							   										  (job-shop-task-duration taskA))))			
			)
		)

		(return-from setup-init-state state)
	)
)

(defun make-state-from-problem (problem)

	(make-state 
		:jobs-lst (job-shop-problem-jobs problem)
		:n.machines (job-shop-problem-n.machines problem)
		:n.jobs (job-shop-problem-n.jobs problem)
		:precedence-solved 0			
		)
	)

(defun copy-task (task)

	(if (not (null task))

		(make-job-shop-task 

			:job.nr (job-shop-task-job.nr task)
			:task.nr (job-shop-task-task.nr task)
			:machine.nr (job-shop-task-machine.nr task)
			:duration (job-shop-task-duration task)
			:start.time (job-shop-task-start.time task)

		)
	)
)


(defun copy-job (state)

	(let ((lst (list)))

		(loop for task in (job-shop-job-tasks state)
			
			do (setf lst (nconc lst (list (copy-task task))))
		)

		(make-job-shop-job
			:job.nr (job-shop-job-job.nr state)
			:tasks lst
			)
	)
)

(defun copy-astate (state)

	(let ((lst (list)))

		(loop for job in (state-jobs-lst state)
			
			do  (setf lst (nconc lst (list (copy-job job))))
		)

		(make-state 
				:jobs-lst lst
				:n.machines (state-n.machines state)
				:n.jobs (state-n.jobs state)
				:heuristic-eval (state-heuristic-eval state)
				:precedence-solved 0
		)
	)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                    		States Comparison		                    ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defun eq-tasks? (task-a task-b)

	(and 

		(equal (job-shop-task-job.nr task-a) (job-shop-task-job.nr task-b))

		(equal (job-shop-task-task.nr task-a) (job-shop-task-task.nr task-b))

		(equal (job-shop-task-machine.nr task-a) (job-shop-task-machine.nr task-b))

		(equal (job-shop-task-duration task-a) (job-shop-task-duration task-b))

		(equal (job-shop-task-start.time task-a) (job-shop-task-start.time task-b))
	)
)


(defun eq-jobs? (job-a job-b)

	(loop for a in (job-shop-job-tasks job-a)

  	  	  for b in (job-shop-job-tasks job-b)

  	  		if (null (eq-tasks? a b))

  	 		do (return-from eq-jobs? nil)
  	)
	T
)

(defun eq-states? (state-a state-b)
 
	(loop for a in (state-jobs-lst state-a)

  	  	  for b in (state-jobs-lst state-b)

  	  		if (null (eq-jobs? a b))

  	 		do (return-from eq-states? nil)
  	)
	T
)


; Estado que cumpre as restricoes de capacidade e precedencia

; Uma maquina nao pode ter 2 tarefas em simultaneo

; Tarefa n+1 nao pode ser excecutada antes da tarefa n


(defun is-goal? (state)
	(testCapacityRestriction state)
)



(defun get-machine-tasks (state machine-id)

	(let ((lst (list)))

		(loop for job in (state-jobs-lst state)

			do (setf lst (nconc lst (list 
										(find-if #'(lambda (task) (eql machine-id (job-shop-task-machine.nr task)))
												 (job-shop-job-tasks job)))))
			)
		lst
	)

)

(defun testMachineCapacity (machine-tasks)
		(let* ((machine-tasks2 nil))
			
			(loop for task in machine-tasks
			  do (progn 
				  	(setf machine-tasks2 (remove task (cdr machine-tasks)))
				  	(loop for task2 in machine-tasks2
						
					if (not (or ;Se a tarefa task nao preceder task2
						   	    (precedes-task task task2)
						   	
						   	; e se a tarefa task2 nao preceder task
						   	    (precedes-task task2 task))
						)
						; entao intercetam-se, ou seja, executam ao mesmo tempo, pelo que nao se verifica a restricao
						do (return-from testMachineCapacity nil)
					)
				
			(setf machine-tasks (cdr machine-tasks)))
		)
			T
	)
)


(defun testCapacityRestriction (state)

	(let ((machine-tasks (list)))

		(loop for machine-id from 0 below (state-n.machines state) do

			(progn 
				(setf machine-tasks (get-machine-tasks state machine-id))
				
				(if (not (testMachineCapacity machine-tasks))
				    (return-from testCapacityRestriction nil))
				)
		)	
		T
	)
)


(defun precedes-task (task-a task-b)
	(let ((task-a-time (+ (job-shop-task-start.time task-a)
						  (job-shop-task-duration task-a)))
		  (task-b-start (job-shop-task-start.time task-b)))
		(<= task-a-time task-b-start)	
	)
)

(defun member? (state state-lst)
	(loop for stt in state-lst
		if (eq-states? stt state)
		  do (return-from member? T))
)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                    			Operators			                    ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun gen-capacity-complient-state (state machine)

	(let* ((new-state (copy-astate state))
		 (machine-tasks (get-machine-tasks new-state machine))
		 (machine-tasks2 nil))

		(loop for task in machine-tasks
			  do (progn 
				  	(setf machine-tasks2 (remove task (cdr machine-tasks)))
				  	(loop for task2 in machine-tasks2
						do (progn

						; Se a task nao preceder task2 ou a task2 nao preceder task, quer dizer que se intercetam!!!
						(if (not (or 
									(precedes-task task task2)
									(precedes-task task2 task)))

							(if (> (job-shop-task-duration task) (job-shop-task-duration task2))

								(if (> (job-shop-task-start.time task) (job-shop-task-start.time task2))
									(setf (job-shop-task-start.time task) (+ (job-shop-task-start.time task2)
																		 (job-shop-task-duration task2)))
									(setf (job-shop-task-start.time task2) (+ (job-shop-task-start.time task)
																		 (job-shop-task-duration task))))
								(setf (job-shop-task-start.time task2) (+ (job-shop-task-start.time task)
																		 (job-shop-task-duration task))))
								
							)
						)) 
				  	(setf machine-tasks (cdr machine-tasks)))
			  	)
	new-state
	)
)

(defun maintain-precedence-restriction (state)

	(loop for job in (state-jobs-lst state)
		do (loop for taskA in (job-shop-job-tasks job)
				 for taskB in (cdr (job-shop-job-tasks job))
				 if (< (job-shop-task-start.time taskB) (+ (job-shop-task-start.time taskA)
				 										   (job-shop-task-duration taskA)))
				 do (progn 
				 		(setf (job-shop-task-start.time taskB) (+ (job-shop-task-start.time taskA)
				 										      (job-shop-task-duration taskA)))
				 		(incf (state-precedence-solved state)))
				 ))

)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                           Expand function                             ;

;				 generates the next possible states                     ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defun expand (state)
	(let ((successors (list))
		  (new-state nil))
		  
		(loop for machine from 0 below (state-n.machines state)

		  	do (progn					
		  			(setf new-state (gen-capacity-complient-state state machine))
		  			(maintain-precedence-restriction new-state)

					(if (or (null successors) (not (eq-states? new-state state)) (not (member? new-state successors)))			    
		  				(setf successors (append successors (list new-state))))
		  			)		
		  	)
			(setq *ALL-GEN-STATES* (append *ALL-GEN-STATES* successors))
			successors	
	)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                        Heuristic Functions                            ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tempo que demora a executar todas as tarefas (quanto maior a duracao pior)
(defun longest-end-time (state)
	(let ((value 0)
		  (task-time 0)
		  (machine-tasks nil))

		(loop for machine from 0 below (state-n.machines state) do
			(progn 
				(setf machine-tasks (get-machine-tasks state machine))
				(loop for task in machine-tasks

					do (progn 
							(setf task-time (+ (job-shop-task-start.time task) (job-shop-task-duration task))) 
							(if (> task-time value)
								(setf value task-time))
							)
					))
		)
	value
	)
)
	

(defun heuristic-max (state)

	(let ((value 0)
		  (evaluation (longest-end-time state)))

		(cond ((is-goal? state) (setf value 0))
			((> (count-state state *ALL-GEN-STATES*) 1) (setf value most-positive-fixnum))
			((null (state-heuristic-eval state)) (setf value evaluation)) 
			((> evaluation (state-heuristic-eval state)) (setf value most-positive-fixnum))
			(T (setf value (+ evaluation (state-precedence-solved state)))))

		(setf (state-heuristic-eval state) value)
	value
	)
)

;Numero de conflitos da restricao de capacidade 

(defun num-conflicts-to-goal (state)
	(let ((value 0)
		 (task-lst nil))

		(loop for machine from 0 below (state-n.machines state) do
			(progn 
				(setf task-lst (get-machine-tasks state machine))
				(loop for task1 in task-lst
					for task2 in (cdr task-lst)
					if (not (or (precedes-task task1 task2)
						  (precedes-task task2 task1)))
					do (incf value))))

	value
	)
)

(defun count-state (state lst)
	(let ((count 0))
		(loop for st in lst 
			if (eq-states? state st)
				do (progn (incf count)
						  (if (> count 1)
						  	(return-from count-state count))))
		count
	)
)

(defun heuristic-conflicts (state)
	(let ((value 0)
		 (conflicts (num-conflicts-to-goal state)))

		(cond ((is-goal? state) (setf value 0))
			((> (count-state state *ALL-GEN-STATES*) 1) (setf value most-positive-fixnum))
			((null (state-heuristic-eval state)) (setf value conflicts)) 
			((> conflicts (state-heuristic-eval state)) (setf value most-positive-fixnum))
			(T (setf value (+ conflicts (state-precedence-solved state)))))

		(setf (state-heuristic-eval state) value)

		value)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                       Auxiliary Functions                             ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Funções auxiliares para ordenar sucessores de acordo com cada heurística
(defun max-end-sort-successors (state1 state2)
        (< (longest-end-time state1) (longest-end-time state2)))
        
(defun heuristic-max-sort-successors (state1 state2)
        (< (heuristic-max state1) (heuristic-max state2)))
        
(defun num-conflicts-to-goal-sort-successors (state1 state2)
        (< (num-conflicts-to-goal state1) (num-conflicts-to-goal state2)))
        
(defun heuristic-conflicts-sort-successors (state1 state2)
        (< (heuristic-conflicts state1) (heuristic-conflicts state2)))

;; Recebe o tempo inicial da contagem e o número de segundos desejados          
(defun time-is-up? (tempo-inicio n-segundos)
        (<= (* n-segundos INTERNAL-TIME-UNITS-PER-SECOND) (- (get-time) tempo-inicio)))

;; Devolve o tempo interno actual
(defun get-time ()
                (get-internal-run-time))

;; Ordena sucessores de acordo com uma heuristica
(defun sort-successors (state)
  (let((position  0)
	(successors (list)))
	
	(setf successors (expand state))
	
	(loop for successor in successors
	  do
	    (setf (state-heuristic-eval successor) (heuristic-conflicts successor)))
	    
	(setf successors (sort successors #'< :key #'state-heuristic-eval))
	
	(loop for successor in successors 
	    do 
	    (progn 
	    	(setf (state-discrepancy successor) position)
	    	(incf position)))
	successors))

(defun next-random-state (successors)
        (let ((n-random (random (length successors))))
                (nth n-random successors)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;			Alternative Approach				;
;                    	Simulated Annealing                             ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cool-temperature (temperature cooling-rate)
	(* temperature (- 1 cooling-rate)))

(defun acceptance-probability (cost1 cost2 temperature)
	(if (< cost2 cost1)
		1
		(cond ((and (eql cost1 most-positive-fixnum)  (eql cost2 most-positive-fixnum)) 1)
			  ((eql cost1 most-positive-fixnum) (exp (/ cost2 temperature)))
			  ((eql cost2 most-positive-fixnum) (exp (/ cost1 temperature)))
			  (t (exp (/ (- cost1 cost2 temperature)))))))
			

(defun random-number ()
	(let ((n (random 1000)))
		(/ n 1000)))

(defun simulated-annealing-iteration (state temperature cooling-rate heuristic)
	(let ((successor nil)
		  (successors (list)))
		(setf successors (expand state))
		(incf *EXPANDED*)
		(cond 
		  ((< temperature 1) (return-from simulated-annealing-iteration state))
		  
		  ((null successors) (return-from simulated-annealing-iteration nil))
		  
		  (t (progn
			(setf successor (next-random-state successors))
			

			(if(is-goal? successor)
				(return-from simulated-annealing-iteration successor)

			(if(> (acceptance-probability (funcall heuristic state) (funcall heuristic successor) temperature) (random-number))
					(simulated-annealing-iteration successor (cool-temperature temperature cooling-rate) cooling-rate heuristic)

			(simulated-annealing-iteration state (cool-temperature temperature cooling-rate) cooling-rate heuristic))))))))

(defun simulated-annealing (state heuristic)
	(let ((solution nil)
		  (temperature 10000)
		  (cooling-rate 0.03)
		  (time (get-internal-real-time)))

		(loop do

			(setf solution (simulated-annealing-iteration state temperature cooling-rate heuristic))

		while (null (is-goal? solution)))
	(list (list solution) (- (get-internal-real-time) time) (list-length *ALL-GEN-STATES*) *EXPANDED*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;			Alternative Approach				;
;                    Limited Discrepancy Search                         ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
		  
(defun lds-discrepancies (state max-discrepancy discrepancy)
	(let ((kmax max-discrepancy)
		  (k discrepancy)
		  (successors (list)))

			(setf successors (sort-successors state))
			(format t "~%~% Nr successors ~D~%" (length successors))

			(if(null successors)
					(return-from lds-discrepancies nil)

			(loop for successor in successors do
			
				(cond
				  ((is-goal? successor) (return-from lds-discrepancies successor))
				  ((state-explorado? successor) (return-from lds-discrepancies nil))
				  ((<= (+ k (state-discrepancy successor)) kmax) (progn									
									  (setf (state-explorado? successor) t)
									  (format t "~%~% Heuristica ~D~%" (state-heuristic-eval successor))
									  (lds-discrepancies successor kmax (+ k (state-discrepancy successor))))))))))		
							  

(defun lds (state)
  (let ((solution nil)
	(discrepancy 0))
	
    (loop do 
		(progn 
			(setf solution (lds-discrepancies state discrepancy 0))
			(format t "~%~% Kmax ~D~%" discrepancy) 
			(incf discrepancy))	;; Incrementa número de discrepâncias para a próxima iteração

	while(null solution))
	
    solution))
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                       Improved Limited Discrepancy Search             ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
		  
(defun ilds-discrepancies (state max-discrepancy discrepancy depth)
	(let ((kmax max-discrepancy)
		  (k discrepancy)
		  (d depth)
		  (successors (list)))

			(setf successors (sort-successors state))

			(if(null successors)
				(return-from ilds-discrepancies nil)

			(loop for successor in successors do
			
			    
				(if(state-explorado? successor)
					(return-from ilds-discrepancies nil)
					
				(if(= kmax 0)
					(progn
						(format t "~%~% Heuristica ~D~%" (state-heuristic-eval successor))
						(if(is-goal? successor)
							(progn
								(format t "~%~% Heuristica ~D~%" (state-heuristic-eval successor))
								(return-from ilds-discrepancies successor))
							
						(if(= (state-discrepancy successor) 0)
									(progn
											(setq MAX-DEPTH (+ 1 d))
											(setf (state-explorado? successor) t)
											(ilds-discrepancies successor kmax k (+ 1 d))))))
				(if(and (> d 0) (<= (+ k (state-discrepancy successor)) kmax))
							(progn
									(setf k (+ k (state-discrepancy successor)))
									(setf (state-explorado? successor) t)
									(ilds-discrepancies successor kmax k (- d 1)))
				(if(= (+ k (state-discrepancy successor)) kmax)
							(progn 
									(if(is-goal? successor)
										(return-from ilds-discrepancies successor)))))))))))

(defun ilds (state)
  (let ((solution nil)
	(discrepancy 0))
	
    (loop do 
		(progn 
			(setf solution (ilds-discrepancies state discrepancy 0 MAX-DEPTH))
			(format t "~%~% KMAX ~D~%" MAX-DEPTH)
			(incf discrepancy))
	while(null solution))
	
    solution))
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                       Iterative Sampling Search                       ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun iteration-iterative-sampling (state)
  (let((successors (list)))
	(if(is-goal? state)
	    state
	(progn
	    (setf successors (expand state))
	    (incf *EXPANDED*)
	    (if(null successors)
		  nil
	    (iteration-iterative-sampling (next-random-state successors)))))))

(defun iterative-sampling (state)
  (let ((initial-time (get-time))
	(solution nil)
	(time (get-internal-real-time)))

      (loop do
      
		(if (time-is-up? initial-time MAX-SECONDS)
	   			(return-from iterative-sampling solution)
	    
		(setf solution (iteration-iterative-sampling state)))
	
      while(null solution))
  (list (list solution) (- (get-internal-real-time) time) (list-length *ALL-GEN-STATES*) *EXPANDED*)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;                        Problem-Solving Function                       ;

; solve - if a given problem has a solution this function will get it   ;

; depending on the method/strategy used for its search.                 ;

; process-result - converts solve's result to desired result format     ;

; show-steps - prints the resolution step by step                       ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun show-steps (list-a)
	(let ((n 0))

		(progn

			(format t "~%********** BEGIN **********~%")

				(loop for state in (car list-a) do

					(progn
						(format t "~%~% Problem ~D~%" n)

						(loop for job in (state-jobs-lst state) do

							(loop for task in (job-shop-job-tasks job) do

								(print task)
							)
						)

						(setf n (1+ n)) 
					)
		
				)

			(format t "~%~%*********** END ***********~%~%")
		)	
	)
)

(defun show-successors (states)
	(let ((n 0))
		(loop for state in states do

			(progn
				(format t "~%~% State ~D~%" n)

				(loop for job in (state-jobs-lst state) do

					(loop for task in (job-shop-job-tasks job) do

						(print task)
					)
				)

				(setf n (1+ n)) 
			)
		)
	)
)

(defun print-result (result)
	(let ((state (first (last (first result))))
			(lst (list)))
		(loop for job in (state-jobs-lst state)
			do (loop for task in (job-shop-job-tasks job)
				do (setf lst (append lst (list task)))))
		lst
		)
	)

(defun solve (problem method heuristic)

  	(progn

	   	(setq *RESULT* (procura 

	                      (cria-problema 

	                      		   	(setup-init-state (make-state-from-problem problem))

	                               	(list 	   	#'expand)

	                               	:objectivo? #'is-goal?

	                               	:estado=    #'eq-states?

	                               	:heuristica heuristic)

	                      			method
	                      	)
	   					)
	   	(print-result *RESULT*)
	)
)	    

(defun calendarizacao (problem method)
	(setf *ALL-GEN-STATES* (list))
  	(setf *EXPANDED* 0) 
	(cond ((string-equal method "melhor.abordagem")
		  	(print-result (simulated-annealing (setup-init-state (make-state-from-problem problem)) #'heuristic-max)))

		((string-equal method "abordagem.alternativa")
		  	(print-result (iterative-sampling (setup-init-state (make-state-from-problem problem)))))

		((string-equal method "ILDS")
		  	(ilds (setup-init-state (make-state-from-problem problem))))

		((string-equal method "sondagem.iterativa")
			(print-result (iterative-sampling (setup-init-state (make-state-from-problem problem)))))

	 	((string-equal method "a*.melhor.heuristica")
		  	(funcall 'solve problem "a*" #'heuristic-conflicts))

		((string-equal method "a*.melhor.heuristica.alternativa")
		  	(funcall 'solve problem "a*" #'heuristic-max))

		; Additional strategies

		((string-equal method "LDS")
		  	(lds (setup-init-state (make-state-from-problem problem))))

		((string-equal method "tempora-simulada")
		  	(print-result (simulated-annealing (setup-init-state (make-state-from-problem problem)) #'heuristic-conflicts)))

		(T (funcall 'solve problem method #'heuristic-conflicts)))
	)

 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;