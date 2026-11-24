# Law of a clock configuration with independent exponential clocks

The probability measure on [clock configurations](clock-config.md) `((r₁, r₂), (u₁, u₂))` under
which the residuals `r₁, r₂` and all the interarrival times `u₁ n`, `u₂ n` (`n ∈ ℕ`) are
independent exponentials with rate `1`. It is the product measure

`(Exp(1) ⊗ Exp(1)) ⊗ (Exp(1)^ℕ ⊗ Exp(1)^ℕ)`

on `(ℝ × ℝ) × (ℝ^ℕ × ℝ^ℕ)` with the product σ-algebra, where `Exp(1)` is the exponential law with
rate `1` (with [density](exp-dens.md) `exp(-x)` for `x ≥ 0` and `0` for `x < 0`) and `Exp(1)^ℕ`
is its infinite product.
