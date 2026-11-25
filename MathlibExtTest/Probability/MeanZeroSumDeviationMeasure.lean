/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.MeanZeroSumDeviationMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open MathlibExt.MeasureTheory.MeanZeroSumDeviationMeasureWanted

private noncomputable def step (x : ℝ) : ℝ := (Icc (0 : ℝ) (1 / 2)).indicator (fun _ => 2) x - 1

-- The two half intervals give a genuinely signed, mean-zero sample of variance one.
example : Tendsto (fun n : ℕ => volume {x : Fin n → ℝ |
    (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ ((n : ℝ) + 1) * Real.sqrt n ≤ |∑ i, step (x i)|})
    atTop (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let s := Icc (0 : ℝ) (1 / 2)
  have hs : MeasurableSet s := measurableSet_Icc
  have hsub : s ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl (by norm_num)
  have hmass : μ s = ENNReal.ofReal (1 / 2) := by
    change (volume : Measure ℝ).restrict (Icc 0 1) s = _
    rw [Measure.restrict_apply hs, inter_eq_left.mpr hsub]
    norm_num [s, Real.volume_Icc]
  have htotal : μ univ = 1 := by simp [μ, Real.volume_Icc]
  let : IsProbabilityMeasure μ := ⟨htotal⟩
  have hφ : Integrable (s.indicator (fun _ => (2 : ℝ))) μ :=
    (integrableOn_const (hmass ▸ ENNReal.ofReal_ne_top)).integrable_indicator hs
  have hm : Measurable step := (measurable_const.indicator hs).sub measurable_const
  have hmean : (∫ x, step x ∂μ) = 0 := by
    change (∫ x, s.indicator (fun _ => (2 : ℝ)) x - 1 ∂μ) = 0
    rw [integral_sub hφ (integrable_const 1), integral_indicator hs, setIntegral_const, integral_const]
    norm_num [Measure.real, hmass, htotal]
  have hsq (x : ℝ) : step x ^ (2 : ℕ) = 1 := by
    by_cases hx : x ∈ Icc (0 : ℝ) (1 / 2) <;> norm_num [step, hx]
  have hLp : MemLp step 2 μ := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr <| by
    simp_rw [hsq]
    exact integrable_const 1
  have hpos : 0 < ∫ x, |step x| ^ 2 ∂μ := by
    simp_rw [sq_abs, hsq]
    simp [integral_const, Measure.real, htotal]
  have ha : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  exact tendsto_volume_abs_sum_ge_mul_sqrt step (fun n => (n : ℝ) + 1)
    hLp hmean hpos (fun n => by positivity) ha _ (fun _ _ => Iff.rfl)
