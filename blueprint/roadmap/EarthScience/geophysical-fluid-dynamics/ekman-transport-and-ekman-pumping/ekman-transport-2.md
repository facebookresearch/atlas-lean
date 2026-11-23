# Ekman transport

Ekman transport: for steady wind stress `τ` with no vertical component,
density `ρ₀ > 0` and Coriolis parameter `f ≠ 0`, the vertically integrated
transport `M = ekmanTransport ρ₀ f τ` satisfies `ρ₀ f k̂ × M = τ`, where
`k̂ = (0, 0, 1)` and `×` is Mathlib's cross product `⨯₃`. The depth
coordinate is `z` upward.
