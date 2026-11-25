# For m > 0, k ≥ 0, the forced equation in the oscillator convention

Let `m > 0` and `k ≥ 0`, let `c`, `F` and `Ω` be real numbers and `x : ℝ → ℝ`. Then

`m x''(t) + c x'(t) + k x(t) = F cos (Ω t)` at every time `t`

if and only if

`x''(t) + 2 γ x'(t) + ω₀² x(t) = f cos (Ω t)` at every time `t`,

with the [damping rate](atlas-damping.md) `γ = c / (2 m)`, the
[natural angular frequency](atlas-natural-frequency.md) `ω₀ = √(k / m)` and the
[forcing amplitude](atlas-forcing.md) `f = F / m`. Here `x'` and `x''` are the first and second
derivatives, with the convention that a derivative is `0` where the function is not
differentiable. No sign condition on `c` is needed; `k ≥ 0` makes `ω₀² = k / m`.
