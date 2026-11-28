/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.DerSimonianLaird
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace MathlibExtTest.Probability.Statistics.DerSimonianLaird

open WantedExt.Probability.Statistics.DerSimonianLairdWanted

/-- With unit sampling and between-study variances, estimates `0` and `2` give estimator,
pooled mean, and pooled variance all equal to `1`. -/
example : dlEstimator (fun _ : Fin 2 => 1) ![0, 2] = 1 ∧
    pooledEstimate (fun _ : Fin 2 => 1) 1 ![0, 2] = 1 ∧
    (∑ _i : Fin 2, ((1 : ℝ) + 1)⁻¹)⁻¹ = 1 := by
  have h := equal_variances le_rfl 1 one_pos ![0, 2] 1 zero_le_one
  rw [h.1, h.2.1, h.2.2]
  norm_num [Fin.sum_univ_two, max_def]

/-- With identical observations, the negative untruncated estimate is cut off at zero. -/
example : dlEstimator (fun _ : Fin 2 => 1) (fun _ => 3) = 0 := by
  have h := (equal_variances le_rfl 1 one_pos (fun _ : Fin 2 => 3) 0 le_rfl).1
  norm_num [Fin.sum_univ_two, max_def] at h
  exact h

open MeasureTheory ProbabilityTheory in
/-- Total variances `2` and `4` give optimal variance `4/3`, less than the uniform-weight
variance formula `3/2`. The theorem applies to uniform weights as a competitor. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (δ e : Fin 2 → Ω → ℝ) (m : ℝ) (hmodel : RandomEffectsModel μ δ e ![1, 3] 1) :
    (∫ ω, pooledEstimate ![1, 3] 1 (fun i => m + δ i ω + e i ω) ∂μ) = m ∧
      Var[fun ω => pooledEstimate ![1, 3] 1 (fun i => m + δ i ω + e i ω); μ] = 4 / 3 ∧
      (4 / 3 : ℝ) ≤ Var[fun ω => ∑ i : Fin 2, (1 / 2) * (m + δ i ω + e i ω); μ] ∧
      (4 / 3 : ℝ) < 3 / 2 ∧
      (∑ i : Fin 2, (1 / 2 : ℝ) ^ 2 * ((![1, 3] : Fin 2 → ℝ) i + 1)) = 3 / 2 := by
  have hv (i : Fin 2) : 0 < (![1, 3] : Fin 2 → ℝ) i := by fin_cases i <;> norm_num
  have h := pooledEstimate_optimal (μ := μ) (hk := le_rfl) (v := ![1, 3]) (hv := hv)
    (Δsq := 1) (m := m) (hΔ := zero_le_one) (δ := δ) (e := e) (hmodel := hmodel)
    (c := fun _ => 1 / 2) (hc := by norm_num [Fin.sum_univ_two])
  have hopt : (∑ i : Fin 2, (((![1, 3] : Fin 2 → ℝ) i) + 1)⁻¹)⁻¹ = 4 / 3 := by
    norm_num [Fin.sum_univ_two]
  rw [hopt] at h
  exact ⟨h.1, h.2.1, h.2.2, by norm_num, by norm_num [Fin.sum_univ_two]⟩

section CochranExpectation

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MetaAnalysis
open scoped ENNReal

private abbrev SignOutcomes := Fin 2 × Fin 2 × Fin 2 × Fin 2

private noncomputable def signMeasure : Measure SignOutcomes := (16 : ℝ≥0∞)⁻¹ • Measure.count

local instance : IsProbabilityMeasure signMeasure := by
  have hcard : ENat.card SignOutcomes = 16 := by simp [Fintype.card_prod]
  constructor
  rw [signMeasure, smul_apply, Measure.count_univ, hcard]
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

private def sign (i : Fin 2) : ℝ := if i = 0 then 1 else -1

private def effect (i : Fin 2) (ω : SignOutcomes) : ℝ := ![sign ω.1, sign ω.2.1] i

private def samplingError (i : Fin 2) (ω : SignOutcomes) : ℝ :=
  ![sign ω.2.2.1, 2 * sign ω.2.2.2] i

private theorem integral_signMeasure (f : SignOutcomes → ℝ) :
    (∫ ω, f ω ∂signMeasure) = (1 / 16 : ℝ) * ∑ ω, f ω := by
  rw [signMeasure, integral_smul_measure, integral_count, ENNReal.toReal_inv]
  norm_num [smul_eq_mul, one_div]

-- At the smallest allowed study count, unequal variances give a strictly positive scale.
example : 0 < weightScale (![1, 4] : Fin 2 → ℝ) ∧ weightScale ![1, 4] = 2 / 5 := by
  rw [weightScale_eq_sum_mul_sub]
  norm_num [Fin.sum_univ_two]

-- Independently average `Q` over all sixteen outcomes at `m = 3` and `Δ² = 1`.
example : (∫ ω, cochranQ ![1, 4] (fun i => 3 + effect i ω + samplingError i ω)
    ∂signMeasure) = 7 / 5 := by
  have hv (i : Fin 2) : 0 < (![1, 4] : Fin 2 → ℝ) i := by fin_cases i <;> norm_num
  have hQ (x y : ℝ) : cochranQ ![1, 4] ![x, y] = (x - y) ^ 2 / 5 := by
    rw [cochranQ_eq_sum_sq_sub hv y]
    norm_num [Fin.sum_univ_two]
    ring
  have hQ' (ω : SignOutcomes) :
      cochranQ ![1, 4] (fun i => 3 + effect i ω + samplingError i ω) =
        (sign ω.1 + sign ω.2.2.1 - sign ω.2.1 - 2 * sign ω.2.2.2) ^ 2 / 5 := by
    have h := hQ (3 + sign ω.1 + sign ω.2.2.1) (3 + sign ω.2.1 + 2 * sign ω.2.2.2)
    convert h using 2
    · funext i
      fin_cases i <;> rfl
    · ring
  simp_rw [hQ']
  norm_num [integral_signMeasure, Fintype.sum_prod_type, Fin.sum_univ_two, sign]

-- The same finite law supplies a concrete client; verify all model moments by enumeration.
private theorem signModel : RandomEffectsModel signMeasure effect samplingError ![1, 4] 1 := by
  have hδ (i : Fin 2) : MemLp (effect i) 2 signMeasure := MemLp.of_discrete
  have he (i : Fin 2) : MemLp (samplingError i) 2 signMeasure := MemLp.of_discrete
  have hmeanδ (i : Fin 2) : (∫ ω, effect i ω ∂signMeasure) = 0 := by
    fin_cases i <;>
      norm_num [integral_signMeasure, Fintype.sum_prod_type, Fin.sum_univ_two, effect, sign]
  have hmeane (i : Fin 2) : (∫ ω, samplingError i ω ∂signMeasure) = 0 := by
    fin_cases i <;>
      norm_num [integral_signMeasure, Fintype.sum_prod_type, Fin.sum_univ_two, samplingError, sign]
  refine ⟨hδ, he, hmeanδ, hmeane, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [variance_eq_integral (hδ i).aemeasurable, hmeanδ]
    fin_cases i <;>
      norm_num [integral_signMeasure, Fintype.sum_prod_type, Fin.sum_univ_two, effect, sign]
  · intro i
    rw [variance_eq_integral (he i).aemeasurable, hmeane]
    fin_cases i <;>
      norm_num [integral_signMeasure, Fintype.sum_prod_type, Fin.sum_univ_two, samplingError, sign]
  · intro i j hij
    rw [covariance_eq_sub (hδ i) (hδ j), hmeanδ, hmeanδ, mul_zero, sub_zero]
    fin_cases i <;> fin_cases j <;> (try contradiction) <;>
      norm_num [integral_signMeasure, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.mul_apply,
        effect, sign]
  · intro i j hij
    rw [covariance_eq_sub (he i) (he j), hmeane, hmeane, mul_zero, sub_zero]
    fin_cases i <;> fin_cases j <;> (try contradiction) <;>
      norm_num [integral_signMeasure, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.mul_apply,
        samplingError, sign]
  · intro i j
    rw [covariance_eq_sub (hδ i) (he j), hmeanδ, hmeane, mul_zero, sub_zero]
    fin_cases i <;> fin_cases j <;>
      norm_num [integral_signMeasure, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.mul_apply,
        effect, samplingError, sign]

example : 0 < weightScale (![1, 4] : Fin 2 → ℝ) ∧
    (∫ ω, cochranQ ![1, 4] (fun i => 3 + effect i ω + samplingError i ω) ∂signMeasure) =
      1 + weightScale ![1, 4] := by
  have hv (i : Fin 2) : 0 < (![1, 4] : Fin 2 → ℝ) i := by fin_cases i <;> norm_num
  have h := integral_cochranQ signMeasure le_rfl ![1, 4] hv 1 3 zero_le_one
    effect samplingError signModel
  norm_num at h
  exact h

end CochranExpectation

end MathlibExtTest.Probability.Statistics.DerSimonianLaird
