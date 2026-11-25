# Polynomial regular-sublevel invariance

For a real polynomial `p` in finitely many variables and a polynomial
vector field `F`, suppose the evaluated gradient is nonzero and the evaluated
Lie derivative `mkDerivation ℝ F p` is nonpositive at every zero of `p`.
A supplied solution whose within-interval velocity on `Icc a b` is
`fun i => eval (u t) (F i)`, initially satisfying `eval (u a) p ≤ 0`,
stays in `{x | eval x p ≤ 0}` throughout that closed interval.
Each constraint requires these hypotheses on its entire zero set.
