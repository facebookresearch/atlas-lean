/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.ShiryaevOptimality

/-!
# Wanted: optimality of CUSUM under Lorden's criterion

Statements about the objects of `MathlibExt.Probability.Statistics.SequentialAnalysis`, for
i.i.d. observations whose laws `P₀`, `P₁` are mutually absolutely continuous probability
measures. Every observation process lives on the coordinate space `ℕ → X` with the filtration
`observationFiltration X` of the first `n` observations; alarms are stopping times for it.
Expected delays and times to false alarm are computed as lower Lebesgue integrals in `ℝ≥0∞`, so
no integrability hypothesis is hidden. The optimality of the sequential probability ratio test,
the Wald–Wolfowitz theorem, is proved in `MathlibExt.Probability.Statistics.WaldWolfowitz`, and
Shiryaev's Bayesian optimality of the Shiryaev rule in
`MathlibExt.Probability.Statistics.ShiryaevOptimality`.

## References

* T. L. Lai, *Sequential analysis: some classical problems and new challenges*, Statistica Sinica
  11 (2001) 303–408, §3 (p. 316).
* V. V. Veeravalli and T. Banerjee, *Quickest change detection*, arXiv:1210.5552 (revised
  version dated 27 November 2024).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]

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
