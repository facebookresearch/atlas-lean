# The l-weighted species balance integrates to minus the boundary flux

Let `n` species and `m` reactions be given, with concentrations `c(t, x) ∈ ℝⁿ`, fluxes
`J(t, x) ∈ ℝⁿ`, a stoichiometric matrix `S` (`n × m`), a reaction-rate map `r : ℝⁿ → ℝᵐ`, a
vector `l ∈ ℝⁿ` and real numbers `a`, `b` and `t`. Suppose that:

- for every `x` between `a` and `b` (either order, ends included) and every species `i`,
  `s ↦ cᵢ(s, x)` has derivative `(S r(c(t, x)))ᵢ - ∂ₓJᵢ(t, x)` at `t` (the balance
  `∂ₜc + ∂ₓJ = S r(c)` holds at time `t`, with `∂ₜc` existing), and `Jᵢ(t, ·)` is differentiable at
  `x`;
- `l` is a conservation vector: `∑ᵢ lᵢ Sᵢⱼ = 0` for every reaction `j`;
- for every species `i`, `x ↦ ∂ₜcᵢ(t, x)` and `x ↦ ∂ₓJᵢ(t, x)` are integrable between `a` and `b`.

Here `∂ₜ` and `∂ₓ` are derivatives, taken to be `0` where the function is not differentiable. Then

`∫ₐᵇ ∑ᵢ lᵢ ∂ₜcᵢ(t, x) dx = -(∑ᵢ lᵢ Jᵢ(t, b) - ∑ᵢ lᵢ Jᵢ(t, a))`:

the reaction term drops out, and no no-flux condition is assumed. The integral is oriented, so for
`b < a` both sides change sign together; the reading as an inventory of the box `[a, b]` needs
`a ≤ b`.
