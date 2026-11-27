# Skew Exec

`exec` for skew heaps. Isabelle's `fun` equations cover only the
arity-matching cases (`Empty` with `[]`, `Insert`/`Del_min` with one
element, `Merge` with two); Lean requires a total function, so the
remaining cases return `.leaf`. No lemma uses those cases: the
framework only calls `exec` on `wf` histories, whose argument lists
have exactly the arity length, and `U_bound` closes mismatched-length
cases by the arity hypothesis, not by the fallback value.
