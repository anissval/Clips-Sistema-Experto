
;;;======================================================
;;;   Wine Expert Sample Problem
;;;
;;;   WINEX: El sistema WINe EXpert.
;;;   Este ejemplo selecciona un vino apropiado
;;;   para beber con una comida.
;;;
;;;     CLIPS Version 6.4 Example
;;;
;;;     To execute, merely load, reset and run.
;;;======================================================

(defmodule MAIN (export ?ALL))

;;****************
;;* DEFFUNCTIONS *
;;****************

(deffunction MAIN::ask-question (?question ?allowed-values)
   (print ?question)
   (bind ?answer (read))
   (if (lexemep ?answer) then (bind ?answer (lowcase ?answer)))
   (while (not (member$ ?answer ?allowed-values)) do
      (print ?question)
      (bind ?answer (read))
      (if (lexemep ?answer) then (bind ?answer (lowcase ?answer))))
   ?answer)

;;*****************
;;* INITIAL STATE *
;;*****************

(deftemplate MAIN::attribute
   (slot name)
   (slot value)
   (slot certainty (default 100.0)))

(defrule MAIN::start
  (declare (salience 10000))
  =>
  (set-fact-duplication TRUE)
  (focus QUESTIONS CHOOSE-QUALITIES WINES PRINT-RESULTS))

(defrule MAIN::combine-certainties ""
  (declare (salience 100)
           (auto-focus TRUE))
  ?rem1 <- (attribute (name ?rel) (value ?val) (certainty ?per1))
  ?rem2 <- (attribute (name ?rel) (value ?val) (certainty ?per2))
  (test (neq ?rem1 ?rem2))
  =>
  (retract ?rem1)
  (modify ?rem2 (certainty (/ (- (* 100 (+ ?per1 ?per2)) (* ?per1 ?per2)) 100))))
  
;;******************
;;* QUESTION RULES *
;;******************

(defmodule QUESTIONS (import MAIN ?ALL) (export ?ALL))

(deftemplate QUESTIONS::question
   (slot attribute (default ?NONE))
   (slot the-question (default ?NONE))
   (multislot valid-answers (default ?NONE))
   (slot already-asked (default FALSE))
   (multislot precursors (default ?DERIVE)))
   
(defrule QUESTIONS::ask-a-question
   ?f <- (question (already-asked FALSE)
                   (precursors)
                   (the-question ?the-question)
                   (attribute ?the-attribute)
                   (valid-answers $?valid-answers))
   =>
   (modify ?f (already-asked TRUE))
   (assert (attribute (name ?the-attribute)
                      (value (ask-question ?the-question ?valid-answers)))))

(defrule QUESTIONS::precursor-is-satisfied
   ?f <- (question (already-asked FALSE)
                   (precursors ?name is ?value $?rest))
         (attribute (name ?name) (value ?value))
   =>
   (if (eq (nth$ 1 ?rest) and) 
    then (modify ?f (precursors (rest$ ?rest)))
    else (modify ?f (precursors ?rest))))

(defrule QUESTIONS::precursor-is-not-satisfied
   ?f <- (question (already-asked FALSE)
                   (precursors ?name is-not ?value $?rest))
         (attribute (name ?name) (value ~?value))
   =>
   (if (eq (nth$ 1 ?rest) and) 
    then (modify ?f (precursors (rest$ ?rest)))
    else (modify ?f (precursors ?rest))))

;;*******************
;;* WINEX QUESTIONS *
;;*******************

(defmodule WINE-QUESTIONS (import QUESTIONS ?ALL))

(deffacts WINE-QUESTIONS::question-attributes
  (question (attribute main-component)
            (the-question "¿El componente principal de la comida es carne, pescado o ave? ")
            (valid-answers carne pescado ave unknown))
  (question (attribute has-turkey)
            (precursors main-component is ave)
            (the-question "¿La comida contiene pavo? ")
            (valid-answers si no unknown))
  (question (attribute has-sauce)
            (the-question "¿La comida tiene salsa? ")
            (valid-answers si no unknown))
  (question (attribute sauce)
            (precursors has-sauce is si)
            (the-question "¿La salsa de la comida es picante, dulce, crema o de tomate?")
            (valid-answers salsa picante dulce crema tomate unknown))
  (question (attribute tastiness)
            (the-question "¿El sabor de la comida es delicado, medio o fuerte? ")
            (valid-answers delicado medio fuerte unknown))
  (question (attribute preferred-body)
            (the-question "¿Prefieres generalmente vinos ligeros, medio o completo? ")
            (valid-answers ligeros medio completo unknown))
  (question (attribute preferred-color)
            (the-question "¿Prefieres generalmente los vinos tinto o blanco? ")
            (valid-answers tinto blanco unknown))
  (question (attribute preferred-sweetness)
            (the-question "¿Prefieres generalmente vinos secos, medios o dulces? ")
            (valid-answers secos medios dulces unknown))) 
 
;;******************
;; The RULES module
;;******************

(defmodule RULES (import MAIN ?ALL) (export ?ALL))

(deftemplate RULES::rule
  (slot certainty (default 100.0))
  (multislot if)
  (multislot then))

(defrule RULES::throw-away-ands-in-antecedent
  ?f <- (rule (if and $?rest))
  =>
  (modify ?f (if ?rest)))

(defrule RULES::throw-away-ands-in-consequent
  ?f <- (rule (then and $?rest))
  =>
  (modify ?f (then ?rest)))

(defrule RULES::remove-is-condition-when-satisfied
  ?f <- (rule (certainty ?c1) 
              (if ?attribute is ?value $?rest))
  (attribute (name ?attribute) 
             (value ?value) 
             (certainty ?c2))
  =>
  (modify ?f (certainty (min ?c1 ?c2)) (if ?rest)))

(defrule RULES::remove-is-not-condition-when-satisfied
  ?f <- (rule (certainty ?c1) 
              (if ?attribute is-not ?value $?rest))
  (attribute (name ?attribute) (value ~?value) (certainty ?c2))
  =>
  (modify ?f (certainty (min ?c1 ?c2)) (if ?rest)))

(defrule RULES::perform-rule-consequent-with-certainty
  ?f <- (rule (certainty ?c1) 
              (if) 
              (then ?attribute is ?value with certainty ?c2 $?rest))
  =>
  (modify ?f (then ?rest))
  (assert (attribute (name ?attribute) 
                     (value ?value)
                     (certainty (/ (* ?c1 ?c2) 100)))))

(defrule RULES::perform-rule-consequent-without-certainty
  ?f <- (rule (certainty ?c1)
              (if)
              (then ?attribute is ?value $?rest))
  (test (or (eq (length$ ?rest) 0)
            (neq (nth$ 1 ?rest) with)))
  =>
  (modify ?f (then ?rest))
  (assert (attribute (name ?attribute) (value ?value) (certainty ?c1))))

;;*******************************
;;* CHOOSE WINE QUALITIES RULES *
;;*******************************

(defmodule CHOOSE-QUALITIES (import RULES ?ALL)
                            (import QUESTIONS ?ALL)
                            (import MAIN ?ALL))

(defrule CHOOSE-QUALITIES::startit => (focus RULES))

(deffacts the-wine-rules

  ; Rules for picking the best body

  (rule (if has-sauce is si and 
            sauce is picante)
        (then best-body is completo))

  (rule (if tastiness is delicado)
        (then best-body is ligero))

  (rule (if tastiness is medio)
        (then best-body is ligero with certainty 30 and
              best-body is medio with certainty 60 and
              best-body is completo with certainty 30))

  (rule (if tastiness is fuerte)
        (then best-body is medio with certainty 40 and
              best-body is completo with certainty 80))

  (rule (if has-sauce is si and
            sauce is crema)
        (then best-body is medio with certainty 40 and
              best-body is completo with certainty 60))

  (rule (if preferred-body is completo)
        (then best-body is completo with certainty 40))

  (rule (if preferred-body is medio)
        (then best-body is medio with certainty 40))

  (rule (if preferred-body is ligero) 
        (then best-body is ligero with certainty 40))

  (rule (if preferred-body is ligero and
            best-body is completo)
        (then best-body is medio))

  (rule (if preferred-body is completo and
            best-body is ligero)
        (then best-body is medio))

  (rule (if preferred-body is unknown) 
        (then best-body is ligero with certainty 20 and
              best-body is medio with certainty 20 and
              best-body is completo with certainty 20))

  ; Rules for picking the best color

  (rule (if main-component is carne)
        (then best-color is tinto with certainty 90))

  (rule (if main-component is ave and
            has-turkey is no)
        (then best-color is blanco with certainty 90 and
              best-color is tinto with certainty 30))

  (rule (if main-component is aves and
            has-turkey is si)
        (then best-color is tinto with certainty 80 and
              best-color is blanco with certainty 50))

  (rule (if main-component is pescado)
        (then best-color is blanco))

  (rule (if main-component is-not pescado and
            has-sauce is si and
            sauce is tomate)
        (then best-color is tinto))

  (rule (if has-sauce is si and
            sauce is crema)
        (then best-color is blanco with certainty 40))
                   
  (rule (if preferred-color is tinto)
        (then best-color is tinto with certainty 40))

  (rule (if preferred-color is blanco)
        (then best-color is blanco with certainty 40))

  (rule (if preferred-color is unknown)
        (then best-color is tinto with certainty 20 and
              best-color is blanco with certainty 20))
  
  ; Rules for picking the best sweetness

  (rule (if has-sauce is si and
            sauce is dulce)
        (then best-sweetness is dulce with certainty 90 and
              best-sweetness is medio with certainty 40))

  (rule (if preferred-sweetness is seco)
        (then best-sweetness is seco with certainty 40))

  (rule (if preferred-sweetness is medio)
        (then best-sweetness is medio with certainty 40))

  (rule (if preferred-sweetness is dulce)
        (then best-sweetness is dulce with certainty 40))

  (rule (if best-sweetness is dulce and
            preferred-sweetness is seco)
        (then best-sweetness is medio))

  (rule (if best-sweetness is seco and
            preferred-sweetness is dulce) 
        (then best-sweetness is medio))

  (rule (if preferred-sweetness is unknown)
        (then best-sweetness is seco with certainty 20 and
              best-sweetness is medio with certainty 20 and
              best-sweetness is dulce with certainty 20))

)

;;************************
;;* WINE SELECTION RULES *
;;************************

(defmodule WINES (import MAIN ?ALL))

(deffacts any-attributes
  (attribute (name best-color) (value any))
  (attribute (name best-body) (value any))
  (attribute (name best-sweetness) (value any)))

(deftemplate WINES::wine
  (slot name (default ?NONE))
  (multislot color (default any))
  (multislot body (default any))
  (multislot sweetness (default any)))

(deffacts WINES::the-wine-list 
  (wine (name Gamay) (color tinto) (body medio) (sweetness medio dulce))
  (wine (name Chablis) (color blanco) (body ligero) (sweetness seco))
  (wine (name Sauvignon-Blanc) (color blanco) (body medio) (sweetness seco))
  (wine (name Chardonnay) (color blanco) (body medio completo) (sweetness medio seco))
  (wine (name Soave) (color blanco) (body ligero) (sweetness medio seco))
  (wine (name Riesling) (color blanco) (body ligero medio) (sweetness medio dulce))
  (wine (name Geverztraminer) (color blanco) (body completo))
  (wine (name Chenin-Blanc) (color blanco) (body ligero) (sweetness medio dulce))
  (wine (name Valpolicella) (color tinto) (body ligero))
  (wine (name Cabernet-Sauvignon) (color tinto) (sweetness seco medio))
  (wine (name Zinfandel) (color tinto) (sweetness seco medio))
  (wine (name Pinot-Noir) (color tinto) (body medio) (sweetness medio))
  (wine (name Burgundy) (color tinto) (body completo))
  (wine (name Zinfandel) (color tinto) (sweetness seco medio)))
  
(defrule WINES::generate-wines
  (wine (name ?name)
        (color $? ?c $?)
        (body $? ?b $?)
        (sweetness $? ?s $?))
  (attribute (name best-color) (value ?c) (certainty ?certainty-1))
  (attribute (name best-body) (value ?b) (certainty ?certainty-2))
  (attribute (name best-sweetness) (value ?s) (certainty ?certainty-3))
  =>
  (assert (attribute (name wine) (value ?name)
                     (certainty (min ?certainty-1 ?certainty-2 ?certainty-3)))))

;;*****************************
;;* PRINT SELECTED WINE RULES *
;;*****************************

(defmodule PRINT-RESULTS (import MAIN ?ALL))

(defrule PRINT-RESULTS::header ""
   (declare (salience 10))
   =>
   (println)
   (println "        SELECTED WINES" crlf)
   (println " WINE                  CERTAINTY")
   (println " -------------------------------")
   (assert (phase print-wines)))

(defrule PRINT-RESULTS::print-wine ""
  ?rem <- (attribute (name wine) (value ?name) (certainty ?per))		  
  (not (attribute (name wine) (certainty ?per1&:(> ?per1 ?per))))
  =>
  (retract ?rem)
  (format t " %-24s %2d%%%n" ?name ?per))

(defrule PRINT-RESULTS::remove-poor-wine-choices ""
  ?rem <- (attribute (name wine) (certainty ?per&:(< ?per 20)))
  =>
  (retract ?rem))

(defrule PRINT-RESULTS::end-spaces ""
   (not (attribute (name wine)))
   =>
   (println))
