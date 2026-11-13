# Integral balance in divergence form

**Integral balance in divergence form** (MF08.2), conditional on the divergence theorem.
Let `Ω` be a compact subset of `ℝⁿ = Fin n → ℝ` with Lebesgue measure, let the density `u` be
jointly `C¹`, let `q t` be the flux field at time `t` with divergence
`FokkerPlanck.divergence (q t) = ∑ᵢ ∂ᵢ (q t)ᵢ`, and let `s t` be integrable on `Ω`. If the
local law `∂ₜu + div q = s` holds at time `t` on `Ω`, and `integral_div_eq_boundary` states the
divergence theorem `∫_Ω div q = Φ t` with `Φ t` the outward flux through the boundary, then
`d/dt ∫_Ω u = -Φ t + ∫_Ω s`. The divergence theorem is a hypothesis, not a result.
For `Ω = [a, b]` with `a ≤ b`, the outward flux is `q t b - q t a`, matching
`integralBalance` with increasing endpoint orientation.
