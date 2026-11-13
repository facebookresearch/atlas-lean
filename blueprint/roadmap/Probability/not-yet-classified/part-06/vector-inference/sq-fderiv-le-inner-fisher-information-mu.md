# Cramér–Rao inequality, directional form

Let `p θ'` be positive probability densities
with respect to `ν` for `θ'` near `θ`, differentiable in the parameter at `θ`, with a
measurable score of finite second moment under `p θ ν`, and let `T` be an estimator with
finite second moment that is unbiased for `g θ'` near `θ`, with `g` differentiable at `θ`. If,
along the line through `θ` in direction `u`, `∫ p dν` and `∫ T p dν` can be differentiated
under the integral sign at `θ`, then `(Dg(θ) u)² ≤ ⟪I(θ) u, u⟫ · Var_θ T`.

The proof applies the one-parameter `FisherInformation.sq_deriv_le_fisherInformation_mul` to the
submodel `t ↦ p (θ + t • u)` and identifies its information by
`inner_fisherInformation_self`.

## Sources

- Rao (1945), Cramér (1946), ch. 32 (several parameters); Lehmann & Casella (1998), Theorem 2.6.6.
