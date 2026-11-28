# Karush–Kuhn–Tucker conditions with mixed constraints under LICQ

Mixed-constraint Karush–Kuhn–Tucker necessary conditions under LICQ. Minimize `f` subject to finitely many inequality constraints `g i y ≤ 0` and equality
constraints `h j y = 0` on a finite-dimensional real normed space. If `x` is feasible, is a
local minimum of `f` on the feasible set, `f` and every `g i` are differentiable at `x`, every
`h j` is `C¹` at `x`, and the derivatives of all equality constraints together with the
derivatives of the active inequality constraints are linearly independent (LICQ), then there
are inequality multipliers `lam ≥ 0` with complementary slackness and free equality multipliers
`mu` such that `fderiv f x + ∑ i, lam i • fderiv (g i) x + ∑ j, mu j • fderiv (h j) x = 0`.

## Sources

- J. Nocedal and S. J. Wright, *Numerical Optimization*, 2nd ed., Springer, 2006, Chapter 12 (first-order necessary conditions under LICQ). Sign conventions: both statements minimize `f`. The book writes inequality constraints as `cᵢ(y) ≥ 0` and its Lagrangian as `f - ∑ λᵢ cᵢ`; taking `cᵢ = -g i` for the inequalities and `cⱼ = h j` for the equalities, its multipliers are `lam i` on the inequalities and `-mu j` on the equalities. Regularity: the book works in `ℝⁿ` and assumes `f` and every constraint continuously differentiable. Here `E` is any finite-dimensional real normed space, `f` and the `g i` need only be differentiable at `x`, and only the `h j` must be `C¹` near `x` (`ContDiffAt ℝ 1`), for the implicit-function step.
