# Case-control sampling shifts only the logistic intercept

**Case-control sampling shifts only the logistic intercept** (Prentice and Pyke 1979). Let
`μ` be a probability measure on `Ω`, let `X : Ω → 𝒳` be a measurable covariate with values in
a finite type with measurable singletons and features `φ : 𝒳 → ℝ^K`, and let `D` (diseased)
and `S` (sampled) be measurable events. Assume:
* the logistic incidence model: `μ(D ∩ {X = x}) = σ(α + β ⬝ φ(x)) μ({X = x})` for every
  `x`;
* sampling depends on disease status only: `μ(S ∩ D ∩ {X = x}) = π₁ μ(D ∩ {X = x})` and
  `μ(S ∩ Dᶜ ∩ {X = x}) = π₀ μ(Dᶜ ∩ {X = x})` for every `x`, with sampling probabilities
  `0 < π₁ ≤ 1` and `0 < π₀ ≤ 1`.

Then for every covariate value `x` with `μ({X = x}) > 0`, the disease probability among the
sampled, `μ(D ∩ S ∩ {X = x}) / μ(S ∩ {X = x})`, equals `σ(α + log (π₁ / π₀) + β ⬝ φ(x))`.
Here `σ` is the logistic function `Real.sigmoid`.

## Sources

- Prentice and Pyke (1979).
