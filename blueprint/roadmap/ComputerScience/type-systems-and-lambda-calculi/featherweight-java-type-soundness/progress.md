# Progress for the call-by-value `Step`, modulo failed casts

A closed well-typed
 expression is a value, is stuck at a failed cast in evaluation position, or steps. No
 class-table property is assumed. The Isabelle/HOL theory (Section 3.8) strengthens the TOPLAS
 progress lemmas (Theorem 2.4.2) by a decomposition: a closed well-typed expression is a value
 or contains a potential redex. This three-way classification refines it for the evaluation
 contexts of Lecture #30: the redex is in evaluation position, and a cast redex
 `(T) (new K(v̄))` steps when `K <: T` and is a failed cast otherwise.
