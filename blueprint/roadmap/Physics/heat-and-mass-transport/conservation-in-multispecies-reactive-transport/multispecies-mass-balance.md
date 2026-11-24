# The conserved inventory changes only by the net boundary flux

Let `n` species and `m` reactions be given, with concentrations `c(t, x) ∈ ℝⁿ`, fluxes
`J(t, x) ∈ ℝⁿ`, a stoichiometric matrix `S` (`n × m`), a reaction-rate map `r : ℝⁿ → ℝᵐ`, a
vector `l ∈ ℝⁿ` and real numbers `a`, `b` and `t`. Suppose that:

- for every `x` between `a` and `b` (either order, ends included) and every species `i`,
  `s ↦ cᵢ(s, x)` has derivative `(S r(c(t, x)))ᵢ - ∂ₓJᵢ(t, x)` at `t` (the balance
  `∂ₜc + ∂ₓJ = S r(c)` holds at time `t`, with `∂ₜc` existing), and `Jᵢ(t, ·)` is differentiable at
  `x`;
- `l` is a conservation vector: `∑ᵢ lᵢ Sᵢⱼ = 0` for every reaction `j`;
- for every species `i`, `x ↦ ∂ₜcᵢ(t, x)` and `x ↦ ∂ₓJᵢ(t, x)` are integrable between `a` and `b`.

Here `∂ₜ` and `∂ₓ` are derivatives, taken to be `0` where the function is not differentiable.
Suppose moreover that, for every species `i`, `s ↦ ∫ₐᵇ cᵢ(s, x) dx` has derivative
`∫ₐᵇ ∂ₜcᵢ(t, x) dx` at `t` (differentiation under the integral sign), and `x ↦ cᵢ(s, x)` is
integrable between `a` and `b` at every time `s`. Then the conserved inventory
`s ↦ ∫ₐᵇ ∑ᵢ lᵢ cᵢ(s, x) dx` has derivative

`-(∑ᵢ lᵢ Jᵢ(t, b) - ∑ᵢ lᵢ Jᵢ(t, a))`

at `t` ([integrated balance](multispecies-integrated.md)). The integrals are oriented; the
inventory reading needs `a ≤ b`.
