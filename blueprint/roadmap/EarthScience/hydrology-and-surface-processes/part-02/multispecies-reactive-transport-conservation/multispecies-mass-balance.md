# Multispecies mass balance

Consider species concentrations `c t x : Fin n → ℝ`, fluxes `J t x`, a
stoichiometric matrix `S` and reaction rates `r(c)` on `[a, b]` at time `t`.
Suppose each concentration satisfies `∂ₜ c_i = (S r(c))_i - ∂ₓ J_i` at every
`x` between `a` and `b`, that is, in $[\min(a, b), \max(a, b)]$, each flux is differentiable in `x` there, the time and space
derivatives are integrable over `[a, b]`, each species inventory `∫ₐᵇ c_i` may
be differentiated under the integral sign, and every concentration is
integrable over `[a, b]` at every time. If `l` is a conservation vector, `∑ i,
l i S i j = 0` for every reaction `j`, then the inventory `t ↦ ∫ₐᵇ l ⬝ᵥ c t x
dx` has derivative `-(l ⬝ᵥ J(t, b) - l ⬝ᵥ J(t, a))` at `t`. Without `a ≤ b`
this is a signed identity for the oriented integral.
