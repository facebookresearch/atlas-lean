# Asymptotic normality of a consistent root by linearization

**Asymptotic normality of a consistent root by linearization** (triangular arrays, general
normalizations). Let `Ψₙ(β, ω)` be differentiable in `β` with derivative `Ψ'ₙ(β, ω)`, and let
`Bₙ > 0` (score scale) and `Dₙ > 0` (sensitivity, e.g. `Dₙ = -𝔼[Ψ'ₙ(β₀)]`) be deterministic.
Assume

* the standardized estimating function at the truth converges in distribution,
  `Ψₙ(β₀) / Bₙ ⇒ Y`;
* `β̂ₙ` is (a.e.-)measurable, a root with probability tending to one, and consistent;
* the slope is locally uniformly close to `-Dₙ`: for every `ε > 0` there is `δ > 0` with
  `P(∃ β ∈ [β₀ - δ, β₀ + δ], |Ψ'ₙ(β) + Dₙ| > ε Dₙ) → 0` (outer probability; no measurability
  of this event is required).

Then `Dₙ (β̂ₙ - β₀) / Bₙ ⇒ Y`. The asymptotic variance of `β̂ₙ` is the sandwich
`Bₙ² / Dₙ²` times `Var Y`.
