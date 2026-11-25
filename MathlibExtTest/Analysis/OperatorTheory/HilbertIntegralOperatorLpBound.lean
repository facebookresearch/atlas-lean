/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.HilbertIntegralOperatorLpBound
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Tests for the Hilbert integral operator bound -/

open MeasureTheory Set
open scoped ENNReal
open MathlibExt.Analysis.OperatorTheory.HilbertIntegralOperatorLpBoundWanted

namespace MathlibExtTest.HilbertIntegralOperatorLpBound

-- This input has a jump at zero, where the operator's integral can be singular.
private noncomputable def ramp : ℝ → ℝ := (Ici 0).indicator (fun x ↦ max (1 - x) 0)

example : ramp 0 = 1 := by norm_num [ramp]

example : eLpNorm (fun x : ℝ ↦ ∫ y in Ici 0, ramp y / (x + y)) 2
    (volume.restrict (Ici 0)) < ∞ := by
  have hs : Function.support ramp ⊆ Icc 0 1 := by
    intro x hx
    by_contra h
    apply hx
    by_cases hx' : 0 ≤ x
    · simp [ramp, hx', max_eq_right (by grind : 1 - x ≤ 0)]
    · simp [ramp, hx']
  have hc : ContinuousOn ramp (Ici 0) := by
    refine (show Continuous (fun x : ℝ ↦ max (1 - x) 0) by fun_prop).continuousOn.congr ?_
    intro x hx
    simp [ramp, hx]
  have hcompact := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  have hm : Measurable ramp :=
    (show Continuous (fun x : ℝ ↦ max (1 - x) 0) by fun_prop).measurable.indicator measurableSet_Ici
  have hLp : MemLp ramp 2 (volume.restrict (Ici 0)) := by
    apply hcompact.memLp_of_bound hm.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ici (a := (0 : ℝ)))] with x hx
    rw [ramp, indicator_of_mem hx, Real.norm_of_nonneg (le_max_right (1 - x) 0)]
    exact max_le (sub_le_self _ hx) zero_le_one
  have h := eLpNorm_hilbertIntegralOperator_le 2 (by norm_num)
    (fun g x ↦ ∫ y in Ici 0, g y / (x + y)) (fun _ _ ↦ rfl) ramp hc hcompact
    (hs.trans Icc_subset_Ici_self) _ rfl
  simpa using h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (by simpa using hLp.eLpNorm_lt_top))

end MathlibExtTest.HilbertIntegralOperatorLpBound
