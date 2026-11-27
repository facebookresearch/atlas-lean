# Joint convexity of the matrix relative entropy

**Joint convexity of the matrix relative entropy** (J. A. Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571v1, Theorem 8.1.4; Tropp, *From joint convexity of
quantum relative entropy to a concavity theorem of Lieb*, arXiv:1101.1070v1, Fact 4, which
attributes it to Lindblad). The map `(X, Y) ↦ re tr (X log X) - re tr (X log Y)` is jointly convex
on the set of pairs of positive-definite matrices over `ℝ` or `ℂ`, where `log` is the matrix
function `cfc Real.log`. Tropp's relative entropy `tr (X log X - X log Y - X + Y)` differs from
it by a linear function of `(X, Y)`, so it is jointly convex as well.
