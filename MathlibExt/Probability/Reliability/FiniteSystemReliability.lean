/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Reliability.SystemLifetime
public import MathlibExt.Probability.Reliability.SystemSurvival
public import Mathlib.MeasureTheory.Integral.Layercake

import MathlibExt.Probability.Distributions.PoissonBinomial
import Mathlib.Probability.Distributions.Bernoulli

/-! # Reliability of finite series, parallel, and k-out-of-n systems -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Reliability

/-- A k-out-of-n system operates if at least `k` of its finite set of components are up. -/
def kOutOfNEvent (E : Type*) [Fintype E] (k : ℕ) : Set (StatMech.ConfigSpace E) :=
  {x | k ≤ ∑ e, if x e then 1 else 0}

/-- Turning more components on cannot turn off a k-out-of-n system. -/
theorem isIncreasing_kOutOfNEvent (E : Type*) [Fintype E] (k : ℕ) :
    StatMech.IsIncreasing (kOutOfNEvent E k) := by
  intro x y hxy hx
  change k ≤ ∑ e, if x e then 1 else 0 at hx
  change k ≤ ∑ e, if y e then 1 else 0
  apply hx.trans
  apply Finset.sum_le_sum
  intro e _
  by_cases he : x e = true
  · have hy : y e = true := (Bool.le_iff_imp.mp (hxy e)) he
    simp [he, hy]
  · simp [he]

private theorem ofReal_up_iff (t : ℝ≥0) (x : ℝ) :
    (t : ℝ≥0∞) < ENNReal.ofReal x ↔ (t : ℝ) < x := by
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg t.coe_nonneg]

/-- With mutually independent measurable real component lifetimes, series reliability is the
product of the component reliabilities, while parallel reliability is one minus the product
of their failure probabilities. A component with lifetime equal to `t` is down at `t`.
See NIST/SEMATECH *e-Handbook of Statistical Methods*, §§8.1.8.2–3. -/
theorem series_parallel_system_reliability {Ω E : Type*} [MeasurableSpace Ω] [Fintype E]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : E → Ω → ℝ}
    (hT : iIndepFun T P) (hm : ∀ i, Measurable (T i)) (t : ℝ≥0) :
    let L := fun A ω => systemLifetime E A (fun i => ENNReal.ofReal (T i ω))
    P.real {ω | (t : ℝ≥0∞) < L (seriesEvent E) ω} =
        ∏ i, P.real {ω | (t : ℝ) < T i ω} ∧
      P.real {ω | (t : ℝ≥0∞) < L (parallelEvent E) ω} =
        1 - ∏ i, (1 - P.real {ω | (t : ℝ) < T i ω}) := by
  intro L
  have hs : {ω | (t : ℝ≥0∞) < L (seriesEvent E) ω} =
      ⋂ i ∈ (Finset.univ : Finset E), T i ⁻¹' Ioi (t : ℝ) := by
    ext ω
    change ((t : ℝ≥0∞) < systemLifetime E (seriesEvent E)
      (fun i => ENNReal.ofReal (T i ω))) ↔ _
    rw [lt_systemLifetime_iff E _ _ t (isIncreasing_seriesEvent E), mem_seriesEvent]
    simp [upConfig_apply_eq_true]
  have hp : {ω | (t : ℝ≥0∞) < L (parallelEvent E) ω} =
      {ω | ∃ i ∈ (Finset.univ : Finset E), (t : ℝ) < T i ω} := by
    ext ω
    change ((t : ℝ≥0∞) < systemLifetime E (parallelEvent E)
      (fun i => ENNReal.ofReal (T i ω))) ↔ _
    rw [lt_systemLifetime_iff E _ _ t (isIncreasing_parallelEvent E), mem_parallelEvent]
    simp [upConfig_apply_eq_true]
  constructor
  · rw [hs, measureReal_def, hT.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun _ => Ioi (t : ℝ)) (fun _ _ => measurableSet_Ioi), ENNReal.toReal_prod]
    rfl
  · rw [hp]
    exact parallel_survival_eq_finset hT hm Finset.univ (t : ℝ)

/-- If `n` mutually independent measurable component lifetimes share the survival probability
`p` at time `t`, the reliability of the k-out-of-n system at `t` is the binomial upper tail
from `k` to `n`. Equality of the survival probabilities at this time suffices; the entire
lifetime distributions need not be identical. See NIST/SEMATECH *e-Handbook of Statistical
Methods*, §8.1.8.4. -/
theorem kOutOfN_system_reliability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n k : ℕ} {T : Fin n → Ω → ℝ}
    (hT : iIndepFun T P) (hm : ∀ i, Measurable (T i)) (t : ℝ≥0) (p : ℝ)
    (hp : ∀ i, P.real {ω | (t : ℝ) < T i ω} = p) :
    P.real {ω | (t : ℝ≥0∞) < systemLifetime (Fin n) (kOutOfNEvent (Fin n) k)
        (fun i => ENNReal.ofReal (T i ω))} =
      ∑ j ∈ Finset.Icc k n, (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
  classical
  let b : ℝ → ℕ := (Ioi (t : ℝ)).indicator (1 : ℝ → ℕ)
  let B : Fin n → Ω → ℕ := fun i => b ∘ T i
  have hb : Measurable b := measurable_const.indicator measurableSet_Ioi
  have hi (i : Fin n) : Measurable (B i) := hb.comp (hm i)
  have hB (i : Fin n) : IsBernoulliRV (B i) P p := by
    have he : B i = {ω | (t : ℝ) < T i ω}.indicator (1 : Ω → ℕ) := by
      ext ω
      by_cases h : (t : ℝ) < T i ω <;> simp [B, b, Set.indicator, h]
    have hs : MeasurableSet {ω | (t : ℝ) < T i ω} := (hm i) measurableSet_Ioi
    rw [← hp i, he]
    exact ⟨by simp, hasLaw_indicator_one_bernoulliMeasure hs.nullMeasurableSet⟩
  have hset : {ω | (t : ℝ≥0∞) < systemLifetime (Fin n) (kOutOfNEvent (Fin n) k)
        (fun i => ENNReal.ofReal (T i ω))} = {ω | k ≤ ∑ i, B i ω} := by
    ext ω
    change ((t : ℝ≥0∞) < systemLifetime (Fin n) (kOutOfNEvent (Fin n) k)
      (fun i => ENNReal.ofReal (T i ω))) ↔ _
    rw [lt_systemLifetime_iff _ _ _ t (isIncreasing_kOutOfNEvent _ k)]
    have he (i : Fin n) :
        (if upConfig (Fin n) (fun i => ENNReal.ofReal (T i ω)) t i then (1 : ℕ) else 0)
          = B i ω := by
      simp only [upConfig_apply_eq_true, ofReal_up_iff, B, b, Function.comp_apply,
        Set.indicator_apply, Set.mem_Ioi, Pi.one_apply]
    change (k ≤ ∑ i, if upConfig (Fin n) (fun i => ENNReal.ofReal (T i ω)) t i then 1 else 0)
      ↔ k ≤ ∑ i, B i ω
    simp only [he]
  have htail := measure_le_sum_eq_poissonBinomialTail (p := fun _ : Fin n => p)
    hB (hT.comp (fun _ => b) (fun _ => hb)) hi k
  rw [hset, measureReal_def, htail]
  simp only [poissonBinomialTail, poissonBinomialPMF_const]

/-- The extended mean of a measurable nonnegative real lifetime is the integral of its strict
survival probabilities over positive time. This integral is finite exactly when the lifetime
is integrable. No independence assumption is needed for the mean-lifetime identity. -/
theorem mean_lifetime_eq_survival_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {T : Ω → ℝ} (hm : Measurable T) (hn : ∀ᵐ ω ∂P, 0 ≤ T ω) :
    (∫⁻ ω, ENNReal.ofReal (T ω) ∂P) = (∫⁻ t in Ioi 0, P {ω | t < T ω}) ∧
      ((∫⁻ t in Ioi 0, P {ω | t < T ω}) < ∞ ↔ Integrable T P) := by
  have h := lintegral_eq_lintegral_meas_lt P hn hm.aemeasurable
  refine ⟨h, ?_⟩
  rw [← h]
  exact (hasFiniteIntegral_iff_ofReal hn).symm.trans
    ⟨fun hfin => ⟨hm.aestronglyMeasurable, hfin⟩, Integrable.hasFiniteIntegral⟩

end Reliability
