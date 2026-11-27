/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapQuarter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! # Erdős's unpublished four-ninths upper bound

A complementary pair with values one third and two thirds witnesses the bound.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

private noncomputable def step (a b t : ℝ) : ℝ :=
  (Ico (-1 : ℝ) 0).indicator (fun _ ↦ a) t +
    (Icc (0 : ℝ) 1).indicator (fun _ ↦ b) t

open Classical in
private theorem step_apply (a b t : ℝ) :
    step a b t = if t ∈ continuousSupportInterval then if t < 0 then a else b else 0 := by
  classical
  simp only [step, indicator, continuousSupportInterval, mem_Ico, mem_Icc]
  split_ifs <;> simp_all <;> linarith

private theorem indicator_integrable (a b c : ℝ) :
    Integrable ((Icc a b).indicator (fun _ ↦ c)) :=
  (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc

private theorem step_admissible : ContinuousAdmissible (step (1 / 3) (2 / 3))
    (step (2 / 3) (1 / 3)) := by
  classical
  have hm (a b : ℝ) : Measurable (step a b) :=
    (measurable_const.indicator measurableSet_Ico).add
      (measurable_const.indicator measurableSet_Icc)
  refine ⟨(hm _ _).aemeasurable, (hm _ _).aemeasurable, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [step_apply]
    split_ifs <;> norm_num
  · intro t
    rw [step_apply]
    split_ifs <;> norm_num
  · intro t ht
    simp [step_apply, ht]
  · intro t ht
    simp [step_apply, ht]
  · intro t ht
    simp only [step_apply, ite_eq_left ht]
    split_ifs <;> norm_num
  · unfold step
    rw [integral_add
      ((integrableOn_const measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico)
      (indicator_integrable 0 1 (2 / 3))]
    norm_num [integral_indicator_const, Real.volume_real_Ico, Real.volume_real_Icc]

private theorem overlap_le_integral (x : ℝ) (u : ℝ → ℝ) (hu : Integrable u)
    (hb : ∀ t, step (1 / 3) (2 / 3) t * step (2 / 3) (1 / 3) (x + t) ≤ u t) :
    continuousOverlap (step (1 / 3) (2 / 3)) (step (2 / 3) (1 / 3)) x ≤ ∫ t, u t := by
  have hz (t : ℝ) (ht : t ∉ continuousSupportInterval) :
      continuousOverlapIntegrand (step (1 / 3) (2 / 3)) (step (2 / 3) (1 / 3)) x t = 0 := by
    change step (1 / 3) (2 / 3) t * step (2 / 3) (1 / 3) (x + t) = 0
    rw [step_admissible.zero_outside_f t ht, zero_mul]
  unfold continuousOverlap
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact integral_mono
    ((step_admissible.overlap_integrable x).integrable_of_forall_notMem_eq_zero hz) hu hb

private theorem overlap_le_fourNinths (x : ℝ) :
    continuousOverlap (step (1 / 3) (2 / 3)) (step (2 / 3) (1 / 3)) x ≤ (4 : ℝ) / 9 := by
  classical
  by_cases hx : 0 ≤ x
  · calc
      _ ≤ ∫ t, (Icc (-1 : ℝ) 1).indicator (fun _ ↦ (2 : ℝ) / 9) t := by
        apply overlap_le_integral x _ (indicator_integrable _ _ _)
        intro t
        simp only [step_apply, continuousSupportInterval, indicator, mem_Icc]
        split_ifs <;> norm_num at *; grind
      _ = (4 : ℝ) / 9 := by norm_num [integral_indicator_const, Real.volume_real_Icc]
  · have hx₀ : x ≤ 0 := le_of_not_ge hx
    by_cases hx₁ : x ≤ -1
    · calc
        _ ≤ ∫ t, (Icc (-1 - x) 1).indicator (fun _ ↦ (4 : ℝ) / 9) t := by
          apply overlap_le_integral x _ (indicator_integrable _ _ _)
          intro t
          simp only [step_apply, continuousSupportInterval, indicator, mem_Icc]
          split_ifs <;> norm_num at * <;> grind
        _ ≤ (4 : ℝ) / 9 := by
          simp only [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc,
            smul_eq_mul]
          have hmax : max (1 - (-1 - x)) 0 ≤ 1 := max_le (by linarith) (by norm_num)
          linarith
    · have hx₁' : -1 ≤ x := le_of_not_ge hx₁
      calc
        _ ≤ ∫ t, (Icc (-1 - x) 1).indicator (fun _ ↦ (2 : ℝ) / 9) t +
            (Icc (0 : ℝ) (-x)).indicator (fun _ ↦ (2 : ℝ) / 9) t := by
          apply overlap_le_integral x _
            ((indicator_integrable _ _ _).add (indicator_integrable _ _ _))
          intro t
          simp only [Pi.add_apply, step_apply, continuousSupportInterval, indicator, mem_Icc]
          split_ifs <;> norm_num at * <;> grind
        _ = (4 : ℝ) / 9 := by
          rw [integral_add (indicator_integrable _ _ _) (indicator_integrable _ _ _)]
          simp only [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc,
            smul_eq_mul, sub_zero]
          rw [max_eq_left (by linarith : 0 ≤ 1 - (-1 - x)),
            max_eq_left (by linarith : 0 ≤ -x)]
          ring

/-- **Erdős's unpublished upper bound $4/9$ for the minimum-overlap constant.** The continuous
Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 4/9$.

Source: Erdős, unpublished, recorded by Optimization Problems 1b. -/
public theorem upperBound_Erdos_unpublished_fourNinths_holds :
  upperBound_Erdos_unpublished_fourNinths := by
  refine le_trans (continuousMinimumOverlapConstant_isUniversalLowerBound
    (step (1 / 3) (2 / 3)) (step (2 / 3) (1 / 3)) step_admissible) ?_
  apply csSup_le (continuousOverlapValues_nonempty _ _)
  rintro y ⟨x, _, rfl⟩
  exact overlap_le_fourNinths x

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
