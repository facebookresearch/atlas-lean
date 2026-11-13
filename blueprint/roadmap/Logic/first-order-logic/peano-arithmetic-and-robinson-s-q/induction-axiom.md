# Induction Axiom

The induction axiom for a body `φ` with `k` parameters, where `φ : BoundedFormula
(Fin k) 1` has one bound variable (the induction variable `x`) and `k` free variables
(the parameters `y⃗`):
`∀y⃗ [φ(0, y⃗) → (∀x (φ(x, y⃗) → φ(S x, y⃗))) → ∀x φ(x, y⃗)]`.
The body is built with the parameters free (using `instantiate` and
`substBoundFormula`, which substitute and quantify the induction variable while the
parameters stay free), then `BoundedFormula.relabel` turns the parameters into bound
variables and `.alls` universally closes over them. For `k = 0` this is the
parameter-free induction axiom.

## Sources

- H. Enderton, A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001, §3.4.
