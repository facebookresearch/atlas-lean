# Integrated advection diffusion reaction

Integrated advection-diffusion-reaction balance at time `t`. Let
`c t x` be a tracer concentration, `U` the constant carrier velocity,
`D` the diffusivity and `k` the decay rate, with flux
`J t x = U * c t x - D * ∂ₓ c t x`. If the PDE
`∂ₜc + U ∂ₓc = D ∂ₓₓc - k c` holds at every point of `Set.uIcc a b`
(derivatives written with `deriv`) and the needed interval integrals
exist, then the oriented integral of `∂ₜc` from `a` to `b` equals
`J(t, a) - J(t, b) - k ∫ x in a..b, c t x`. For `a ≤ b` this is the net
inflow into `[a, b]` minus the decayed amount; for `b < a` both sides are
the negatives of the balance on `[b, a]`. The identity holds for all real
`U`, `D`, `k` and concentrations; the diffusion and decay reading needs
`0 ≤ D`, `0 ≤ k` and `0 ≤ c`.
