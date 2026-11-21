-- Copyright (c) 2026 Meta Platforms, Inc. and affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.

module

public import PhyslibExt.EarthScience.WeakParabolic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum

open MeasureTheory
open scoped ContDiff
open Filter
open Set

namespace EarthScience

/-- The quadratic profile `x * (1 - x)` is a `WeakH10` function. -/
noncomputable def quadWeak : WeakH10 where
  toFun := fun x => x * (1 - x)
  weakDeriv := fun x => 1 - 2 * x
  weakDeriv_memLp := by
    refine MemLp.of_bound ?_ 2 ?_
    · exact (continuous_const.sub (continuous_const.mul continuous_id)).aestronglyMeasurable
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
      filter_upwards with x hx
      have hx0 : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 := hx.2
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
  toFun_eq_integral := by
    have hderiv : ∀ t : ℝ, HasDerivAt (fun s => s - s ^ 2) (1 - 2 * t) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      exact h1.sub h2
    have hcont : Continuous (fun t => (1 : ℝ) - 2 * t) :=
      continuous_const.sub (continuous_const.mul continuous_id)
    intro x hx
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable 0 x)]
    ring
  integral_weakDeriv_eq_zero := by
    have hderiv : ∀ t : ℝ, HasDerivAt (fun s => s - s ^ 2) (1 - 2 * t) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      exact h1.sub h2
    have hcont : Continuous (fun t => (1 : ℝ) - 2 * t) :=
      continuous_const.sub (continuous_const.mul continuous_id)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable 0 1)]
    norm_num

example : quadWeak.weakDeriv 0 = 1 := by simp [quadWeak]
example : quadWeak.toFun 0 = 0 := by simp [quadWeak]

/-- The zero function is a `WeakH10` function (boundary case). -/
noncomputable def zeroWeak : WeakH10 where
  toFun := fun _ => 0
  weakDeriv := fun _ => 0
  weakDeriv_memLp := by simp
  toFun_eq_integral := by
    intro x _
    simp
  integral_weakDeriv_eq_zero := by simp

example : zeroWeak.toFun 0 = 0 := rfl
example : zeroWeak.weakDeriv 1 = 0 := rfl

/-- Fubini bridge on the constant function over the unit square. -/
instance : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
  simp [Real.volume_Icc]

example : (∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (1 : ℝ))
    = ∫ p in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, (1 : ℝ)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  exact iterated_eq_product (by norm_num) _ (integrable_const _)

/-- Floor is constant on the first slab of a 2-slab partition of `[0, 1]`. -/
example : Nat.floor ((0.25 - 0) / ((1 - 0) / (2 : ℝ))) = 0 := by
  have h := floor_slab_eq (t0 := (0 : ℝ)) (t1 := (1 : ℝ)) (by norm_num)
    (N := 2) (by norm_num) (k := 0)
    (t := (0.25 : ℝ)) (by
      rw [Set.mem_Ico]
      norm_num)
  exact h

-- The conditional existence/uniqueness theorem typechecks.
#check @weak_parabolic_exists_unique_conditional

end EarthScience
