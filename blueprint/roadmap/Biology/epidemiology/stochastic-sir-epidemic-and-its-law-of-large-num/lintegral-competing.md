# Competing exponential clocks, joint law

Let `P = Exp(1) ⊗ Exp(1)` be the law on `ℝ²` of a pair `r = (r₁, r₂)` of independent exponential
clocks with rate `1` (each with [density](exp-dens.md) `exp(-x)` for `x ≥ 0` and `0` for `x < 0`),
run at speeds `a > 0` and `b ≥ 0`. Channel `1` rings first when `b r₁ < a r₂`, at time
`h = r₁ / a`. For every measurable function `φ : ℝ² → [0, ∞]`,

`∫ 1{b r₁ < a r₂} · φ((a + b) h, r₂ - b h) dP(r) = (a / (a + b)) · ∫ φ dP`,

where `1{b r₁ < a r₂}` is `1` on the event and `0` off it, and the integrals are Lebesgue
integrals of nonnegative functions, with values in `[0, ∞]`. With `φ = 1`, the event
`b r₁ < a r₂` has probability `a / (a + b)`. Conditionally on that event, the total clock
`(a + b) h` and the overshoot `r₂ - b h` of the other channel are again independent exponentials
with rate `1`: their joint law is `P`.
