/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.FixationComparison
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Basic

open Set MeasureTheory MathlibExt.Biology.PopulationGenetics.Diffusion

@[expose] public section
namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.FixationComparison

example : fixationProb (fun _ => (0:ℝ)) (fun x => x * (1 - x)) (1/2)
    = 1/2 := by
  have hReg : IsRegularDiffusion (fun _ : ℝ => (0:ℝ))
      (fun x : ℝ => x * (1 - x)) := {
    pos := fun x hx => mul_pos hx.1 (sub_pos.mpr hx.2)
    continuousOn :=
      (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn
    continuousOn_div := by
      have hA : ContinuousOn (fun x : ℝ => x * (1 - x)) (Ioo 0 1) :=
        (continuous_id.mul
          (continuous_const.sub continuous_id)).continuousOn
      have hNe : ∀ x ∈ Ioo (0:ℝ) 1, (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
        fun x hx => ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
      exact continuousOn_const.div₀ hA hNe
    intervalIntegrable_div := by
      have hEq : EqOn (fun _ : ℝ => (0:ℝ))
          (fun x => (fun _ : ℝ => (0:ℝ)) x / (fun x => x * (1 - x)) x)
          (uIoo 0 1) := by
        intro x hx
        exact (zero_div _).symm
      exact IntervalIntegrable.congr_uIoo intervalIntegrable_const hEq }
  have hNonneg : ∀ x ∈ Ioo (0:ℝ) 1,
      0 ≤ (fun _ : ℝ => (0:ℝ)) x / (fun x : ℝ => x * (1 - x)) x := by
    intro x hx
    rw [zero_div]
  have hNonpos : ∀ x ∈ Ioo (0:ℝ) 1,
      (fun _ : ℝ => (0:ℝ)) x / (fun x : ℝ => x * (1 - x)) x ≤ 0 := by
    intro x hx
    rw [zero_div]
  have hp : (1/2 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have h1 := le_fixationProb_of_nonneg _ _ _ hReg hNonneg hp
  have h2 := fixationProb_le_of_nonpos _ _ _ hReg hNonpos hp
  exact le_antisymm h2 h1

example : (1/2 : ℝ) ≤ fixationProb (fun x => x * (1 - x))
    (fun x => x * (1 - x)) (1/2) := by
  have hReg : IsRegularDiffusion (fun x : ℝ => x * (1 - x))
      (fun x : ℝ => x * (1 - x)) := {
    pos := fun x hx => mul_pos hx.1 (sub_pos.mpr hx.2)
    continuousOn :=
      (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn
    continuousOn_div := by
      have hA : ContinuousOn (fun x : ℝ => x * (1 - x)) (Ioo 0 1) :=
        (continuous_id.mul
          (continuous_const.sub continuous_id)).continuousOn
      have hNe : ∀ x ∈ Ioo (0:ℝ) 1, (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
        fun x hx => ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
      exact hA.div₀ hA hNe
    intervalIntegrable_div := by
      have hEq : EqOn (fun _ : ℝ => (1:ℝ))
          (fun x => (fun x : ℝ => x * (1 - x)) x / (fun x => x * (1 - x)) x)
          (uIoo 0 1) := by
        intro x hx
        rw [uIoo_of_lt (by norm_num : (0:ℝ) < 1)] at hx
        have hNe : (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
          ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
        exact (div_self hNe).symm
      exact IntervalIntegrable.congr_uIoo intervalIntegrable_const hEq }
  have hdrift : ∀ x ∈ Ioo (0:ℝ) 1,
      0 ≤ (fun x : ℝ => x * (1 - x)) x / (fun x : ℝ => x * (1 - x)) x := by
    intro x hx
    have hNe : (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
      ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
    rw [div_self hNe]
    norm_num
  have hp : (1/2 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  exact le_fixationProb_of_nonneg _ _ _ hReg hdrift hp

example : fixationProb (fun x => -(x * (1 - x))) (fun x => x * (1 - x))
    (1/2) ≤ 1/2 := by
  have hReg : IsRegularDiffusion (fun x : ℝ => -(x * (1 - x)))
      (fun x : ℝ => x * (1 - x)) := {
    pos := fun x hx => mul_pos hx.1 (sub_pos.mpr hx.2)
    continuousOn :=
      (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn
    continuousOn_div := by
      have hA : ContinuousOn (fun x : ℝ => x * (1 - x)) (Ioo 0 1) :=
        (continuous_id.mul
          (continuous_const.sub continuous_id)).continuousOn
      have hB : ContinuousOn (fun x : ℝ => -(x * (1 - x))) (Ioo 0 1) :=
        (continuous_id.mul
          (continuous_const.sub continuous_id)).neg.continuousOn
      have hNe : ∀ x ∈ Ioo (0:ℝ) 1, (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
        fun x hx => ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
      exact hB.div₀ hA hNe
    intervalIntegrable_div := by
      have hEq : EqOn (fun _ : ℝ => (-1:ℝ))
          (fun x => (fun x : ℝ => -(x * (1 - x))) x / (fun x => x * (1 - x)) x)
          (uIoo 0 1) := by
        intro x hx
        rw [uIoo_of_lt (by norm_num : (0:ℝ) < 1)] at hx
        have hNe : (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
          ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
        simp only
        rw [neg_div, div_self hNe]
      exact IntervalIntegrable.congr_uIoo intervalIntegrable_const hEq }
  have hdrift : ∀ x ∈ Ioo (0:ℝ) 1,
      (fun x : ℝ => -(x * (1 - x))) x / (fun x : ℝ => x * (1 - x)) x ≤ 0 := by
    intro x hx
    have hNe : (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
      ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
    simp only
    rw [neg_div, div_self hNe]
    norm_num
  have hp : (1/2 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  exact fixationProb_le_of_nonpos _ _ _ hReg hdrift hp

example : (0:ℝ) ≤ fixationProb (fun x => x * (1 - x))
    (fun x => x * (1 - x)) 0 := by
  have hReg : IsRegularDiffusion (fun x : ℝ => x * (1 - x))
      (fun x : ℝ => x * (1 - x)) := {
    pos := fun x hx => mul_pos hx.1 (sub_pos.mpr hx.2)
    continuousOn :=
      (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn
    continuousOn_div := by
      have hA : ContinuousOn (fun x : ℝ => x * (1 - x)) (Ioo 0 1) :=
        (continuous_id.mul
          (continuous_const.sub continuous_id)).continuousOn
      have hNe : ∀ x ∈ Ioo (0:ℝ) 1, (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
        fun x hx => ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
      exact hA.div₀ hA hNe
    intervalIntegrable_div := by
      have hEq : EqOn (fun _ : ℝ => (1:ℝ))
          (fun x => (fun x : ℝ => x * (1 - x)) x / (fun x => x * (1 - x)) x)
          (uIoo 0 1) := by
        intro x hx
        rw [uIoo_of_lt (by norm_num : (0:ℝ) < 1)] at hx
        have hNe : (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
          ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
        exact (div_self hNe).symm
      exact IntervalIntegrable.congr_uIoo intervalIntegrable_const hEq }
  have hdrift : ∀ x ∈ Ioo (0:ℝ) 1,
      0 ≤ (fun x : ℝ => x * (1 - x)) x / (fun x : ℝ => x * (1 - x)) x := by
    intro x hx
    have hNe : (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
      ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
    rw [div_self hNe]
    norm_num
  have hp : (0:ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  exact le_fixationProb_of_nonneg _ _ _ hReg hdrift hp

example : (1:ℝ) ≤ fixationProb (fun x => x * (1 - x))
    (fun x => x * (1 - x)) 1 := by
  have hReg : IsRegularDiffusion (fun x : ℝ => x * (1 - x))
      (fun x : ℝ => x * (1 - x)) := {
    pos := fun x hx => mul_pos hx.1 (sub_pos.mpr hx.2)
    continuousOn :=
      (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn
    continuousOn_div := by
      have hA : ContinuousOn (fun x : ℝ => x * (1 - x)) (Ioo 0 1) :=
        (continuous_id.mul
          (continuous_const.sub continuous_id)).continuousOn
      have hNe : ∀ x ∈ Ioo (0:ℝ) 1, (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
        fun x hx => ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
      exact hA.div₀ hA hNe
    intervalIntegrable_div := by
      have hEq : EqOn (fun _ : ℝ => (1:ℝ))
          (fun x => (fun x : ℝ => x * (1 - x)) x / (fun x => x * (1 - x)) x)
          (uIoo 0 1) := by
        intro x hx
        rw [uIoo_of_lt (by norm_num : (0:ℝ) < 1)] at hx
        have hNe : (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
          ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
        exact (div_self hNe).symm
      exact IntervalIntegrable.congr_uIoo intervalIntegrable_const hEq }
  have hdrift : ∀ x ∈ Ioo (0:ℝ) 1,
      0 ≤ (fun x : ℝ => x * (1 - x)) x / (fun x : ℝ => x * (1 - x)) x := by
    intro x hx
    have hNe : (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
      ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
    rw [div_self hNe]
    norm_num
  have hp : (1:ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  exact le_fixationProb_of_nonneg _ _ _ hReg hdrift hp

example : scaleDensity (fun x => x * (1 - x)) (fun x => x * (1 - x)) (3/4)
    ≤ scaleDensity (fun x => x * (1 - x)) (fun x => x * (1 - x)) (1/4) := by
  have hReg : IsRegularDiffusion (fun x : ℝ => x * (1 - x))
      (fun x : ℝ => x * (1 - x)) := {
    pos := fun x hx => mul_pos hx.1 (sub_pos.mpr hx.2)
    continuousOn :=
      (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn
    continuousOn_div := by
      have hA : ContinuousOn (fun x : ℝ => x * (1 - x)) (Ioo 0 1) :=
        (continuous_id.mul
          (continuous_const.sub continuous_id)).continuousOn
      have hNe : ∀ x ∈ Ioo (0:ℝ) 1, (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
        fun x hx => ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
      exact hA.div₀ hA hNe
    intervalIntegrable_div := by
      have hEq : EqOn (fun _ : ℝ => (1:ℝ))
          (fun x => (fun x : ℝ => x * (1 - x)) x / (fun x => x * (1 - x)) x)
          (uIoo 0 1) := by
        intro x hx
        rw [uIoo_of_lt (by norm_num : (0:ℝ) < 1)] at hx
        have hNe : (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
          ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
        exact (div_self hNe).symm
      exact IntervalIntegrable.congr_uIoo intervalIntegrable_const hEq }
  have hdrift : ∀ x ∈ Ioo (0:ℝ) 1,
      0 ≤ (fun x : ℝ => x * (1 - x)) x / (fun x : ℝ => x * (1 - x)) x := by
    intro x hx
    have hNe : (fun x : ℝ => x * (1 - x)) x ≠ 0 :=
      ne_of_gt (mul_pos hx.1 (sub_pos.mpr hx.2))
    rw [div_self hNe]
    norm_num
  have hAnti := scaleDensity_antitoneOn_of_nonneg _ _ hReg hdrift
  have h14 : (1/4 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have h34 : (3/4 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have hle : (1/4 : ℝ) ≤ 3/4 := by norm_num
  exact hAnti h14 h34 hle

#print axioms le_fixationProb_of_nonneg
#print axioms fixationProb_le_of_nonpos
#print axioms scaleDensity_antitoneOn_of_nonneg
#print axioms scaleDensity_monotoneOn_of_nonpos

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.FixationComparison
