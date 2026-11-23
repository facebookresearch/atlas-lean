/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.WaldInequalities
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Wanted: optimality theorems of sequential testing and quickest change detection

Statements about the objects of `MathlibExt.Probability.Statistics.SequentialAnalysis`, for
i.i.d. observations whose laws `P₀`, `P₁` are mutually absolutely continuous probability
measures. Every observation process lives on the coordinate space `ℕ → X` with the filtration
`observationFiltration X` of the first `n` observations; tests and alarms are stopping times for
it. Expected sample sizes and delays are computed as lower Lebesgue integrals in `ℝ≥0∞`, so no
integrability hypothesis is hidden.

## References

* T. L. Lai, *Sequential analysis: some classical problems and new challenges*, Statistica Sinica
  11 (2001) 303–408, §2 (p. 305) and §3 (p. 316).
* B. Eisenberg, *Sequential probability ratio test*, Encyclopedia of Mathematics.
* V. V. Veeravalli and T. Banerjee, *Quickest change detection*, arXiv:1210.5552 (revised
  version dated 27 November 2024), Theorem 3.1.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- **Wald–Wolfowitz theorem: optimality of the SPRT.** Let `P₀ ≠ P₁` be mutually absolutely
continuous and consider the SPRT with log-boundaries `a < 0 < b`. Let `(T, D)` be any test: a
stopping time `T` of the observations with finite expected value under both hypotheses, and a
rejection region `D` for `P₀` in the stopped `σ`-algebra, whose error probabilities
`P₀(D)` and `P₁(Dᶜ)` do not exceed those of the SPRT. Then the SPRT has smaller expected sample
size under both `P₀` and `P₁`. This is the Wald–Wolfowitz theorem (1948) as stated in Lai 2001,
§2, p. 305, for non-randomised tests; randomised tests are not covered by this statement. -/
theorem_wanted sprt_wald_wolfowitz {P₀ P₁ : Measure X} [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (hne : P₀ ≠ P₁) {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) {T : (ℕ → X) → WithTop ℕ}
    (hT : IsStoppingTime (observationFiltration X) T) {D : Set (ℕ → X)}
    (hD : MeasurableSet[hT.measurableSpace] D)
    (hT₀ : ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀) < ∞)
    (hT₁ : ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₁) < ∞)
    (hα : Measure.infinitePi (fun _ : ℕ => P₀) D ≤
      Measure.infinitePi (fun _ : ℕ => P₀) (sprtAcceptOne P₀ P₁ h₁₀ h₀₁ a b))
    (hβ : Measure.infinitePi (fun _ : ℕ => P₁) Dᶜ ≤
      Measure.infinitePi (fun _ : ℕ => P₁) (sprtAcceptZero P₀ P₁ h₁₀ h₀₁ a b)) :
    ∫⁻ ω, ((show ℕ∞ from sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) : ℝ≥0∞)
        ∂Measure.infinitePi (fun _ : ℕ => P₀) ≤
        ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀) ∧
      ∫⁻ ω, ((show ℕ∞ from sprtTime P₀ P₁ h₁₀ h₀₁ a b ω) : ℝ≥0∞)
        ∂Measure.infinitePi (fun _ : ℕ => P₁) ≤
        ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₁)

/-- **Shiryaev's theorem: Bayesian optimality of the Shiryaev rule.** Let `P₀ ≠ P₁` be mutually
absolutely continuous with `D(P₁ ‖ P₀) < ∞`, let the change point have the geometric prior
`ρ (1 - ρ)^{n-1}` with `0 < ρ < 1`, and let `0 < A < 1` be a threshold whose Shiryaev rule
`τ_S = inf {n ≥ 1 : pₙ ≥ A}` has false-alarm probability exactly `α`. Then `τ_S` minimises the
average detection delay `E[(τ - Γ)⁺]` among all stopping times `τ` with false-alarm probability
`P(τ < Γ) ≤ α` (Veeravalli–Banerjee, Theorem 3.1, crediting Shiryaev 1963 and 1978; the
hypotheses `P₀ ≠ P₁` and `D(P₁ ‖ P₀) < ∞` are that survey's standing assumption
`0 < D(f₁ ‖ f₀) < ∞`). -/
theorem_wanted shiryaevTime_optimal {P₀ P₁ : Measure X} [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (hne : P₀ ≠ P₁)
    (hkl : InformationTheory.klDiv P₁ P₀ ≠ ∞) {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {A : ℝ}
    (hA₀ : 0 < A) (hA₁ : A < 1) {α : ℝ≥0∞}
    (hα : falseAlarmProb P₀ P₁ ρ hρ₀ hρ₁.le (shiryaevTime P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le A) = α)
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (observationFiltration X) τ)
    (hτα : falseAlarmProb P₀ P₁ ρ hρ₀ hρ₁.le τ ≤ α) :
    averageDetectionDelay P₀ P₁ ρ hρ₀ hρ₁.le (shiryaevTime P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le A) ≤
      averageDetectionDelay P₀ P₁ ρ hρ₀ hρ₁.le τ

/-- **Moustakides' theorem: optimality of CUSUM under Lorden's criterion.** Let `P₀ ≠ P₁` be
mutually absolutely continuous, let `c > 0`, and let `γ` be the mean time to false alarm
`E_∞[N_c]` of the CUSUM alarm `N_c = inf {n ≥ 1 : W_n ≥ c}`. Then `N_c` minimises Lorden's
worst-case delay `sup_ν ess sup E_ν[(T - ν + 1)⁺ | X₁, …, X_{ν-1}]` among all stopping times `T`
with `E_∞[T] ≥ γ` (Moustakides 1986, as stated in Lai 2001, §3, p. 316; Lorden 1971 had proved
asymptotic optimality as `γ → ∞`). Lai writes CUSUM with the statistic
`max_{1 ≤ k ≤ n} ∑_{i=k}^{n} log L(Xᵢ)`; for `c > 0` it crosses `c` at the same time as Page's
statistic `W_n` used here (Veeravalli–Banerjee, remark after equation (48)). -/
theorem_wanted cusumTime_lordenDelay_le {P₀ P₁ : Measure X} [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (hne : P₀ ≠ P₁) {c : ℝ}
    (hc : 0 < c) {γ : ℝ≥0∞}
    (hγ : ∫⁻ ω, ((show ℕ∞ from cusumTime P₀ P₁ h₁₀ h₀₁ c ω) : ℝ≥0∞)
      ∂Measure.infinitePi (fun _ : ℕ => P₀) = γ)
    {T : (ℕ → X) → WithTop ℕ} (hT : IsStoppingTime (observationFiltration X) T)
    (hTγ : γ ≤ ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂Measure.infinitePi (fun _ : ℕ => P₀)) :
    lordenDelay P₀ P₁ (cusumTime P₀ P₁ h₁₀ h₀₁ c) ≤ lordenDelay P₀ P₁ T

end MeasureTheory
