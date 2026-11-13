# Johnstone's Tracy–Widom limit

Let `q` be the Hastings–McLeod solution of Painlevé II
(`q'' = s q + 2 q³` with `q(s) · 2 √π s^{1/4} e^{(2/3) s^{3/2}} → 1` as `s → ∞`). Let
`n k, p k → ∞` with `n k / p k → γ ≥ 1`, and let `X` have independent standard Gaussian entries
(`Measure.pi` of `gaussianReal 0 1` over `Fin (n k) × Fin (p k)`). The largest eigenvalue of
`Xᵀ X` is `ℓ₁ = sup_{‖v‖ = 1} ‖X v‖²`. Then for every `s`, the function
`x ↦ q x + (x - s) q x ²` is integrable on `(s, ∞)` and
`P((ℓ₁ - μ_k) / σ_k ≤ s) → F₁(s) = exp (-(1/2) ∫ₛ^∞ (q x + (x - s) q x ²) dx)` with Johnstone's
`μ_k = (√(n - 1) + √p)²` and `σ_k = (√(n - 1) + √p) (1/√(n - 1) + 1/√p)^{1/3}`.

## Sources

- I. M. Johnstone, Ann. Statist. 29 (2001), 295–327, Theorem 1.1; Tracy–Widom (1996) for `F₁`; Hastings–McLeod (1980) for `q`.
