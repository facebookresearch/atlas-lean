# Scalar first-order remainder bound

For `f` twice continuously differentiable
(`ContDiff ℝ 2 f`, hence differentiable at every base point including interval
endpoints) with `|deriv (deriv f) y| ≤ H` on the closed interval `Set.Icc a b`, and
`x`, `x + δ` both in that interval,
`|f (x + δ) - f x - deriv f x * δ| ≤ H / 2 * δ ^ 2`. The proof reuses Mathlib's
`taylor_mean_remainder_lagrange_iteratedDeriv` at `n = 1`. The side conditions are
exact: global `C²` for the derivative identification at the base point, the
second-derivative bound only on `Icc a b`, and both endpoints in `Icc a b`.
