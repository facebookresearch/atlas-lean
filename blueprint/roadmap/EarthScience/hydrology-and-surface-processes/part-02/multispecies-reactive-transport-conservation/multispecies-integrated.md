# Integrated multispecies conservation law

Multispecies reactive-transport conservation on a one-dimensional box
`[a, b]`, at time `t`. Species concentrations are `c t x : Fin n → ℝ`,
fluxes `J t x : Fin n → ℝ`, the stoichiometric matrix is
`S : Fin n → Fin m → ℝ`, and `r : (Fin n → ℝ) → Fin m → ℝ` is the reaction
rate vector. Suppose that at every `x` between `a` and `b`, that is, in $[\min(a, b), \max(a, b)]$, each concentration
`c_i(·, x)` has time derivative `(S *ᵥ r(c))_i - ∂ₓ J_i` at `t` (that is,
`c_t + ∂ₓ J = S *ᵥ r(c)` with `c_t` existing) and each flux `J_i(t, ·)` is
differentiable at `x`, and that each `x ↦ ∂ₜc_i(t, x)` and each `x ↦ ∂ₓJ_i(t, x)` is interval
integrable on `[a, b]`. If `l` is a conservation vector,
`∑ i, l i * S i j = 0` for every reaction `j`, then the integral of
`l ⬝ᵥ c_t` over `[a, b]` equals minus the boundary flux
`l ⬝ᵥ J(t, b) - l ⬝ᵥ J(t, a)`; the reaction term drops out. Without
`a ≤ b` this is a signed identity for the oriented integral `∫ x in a..b`;
the box interpretation requires `a ≤ b`.
