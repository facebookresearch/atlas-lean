/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RegularVariation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace MathlibExtTest.Probability.TailIntegralRVCharacterization

open MathlibExt.Probability.RegularVariation

/-- The old inclusive negative endpoint counts the atom; the strict tail does not. -/
theorem negative_boundary_atom :
    ((Measure.dirac (-1 : ℝ)) (Set.Iic (-1))).toReal = 1 ∧
      leftTail (Measure.dirac (-1 : ℝ)) 1 = 0 ∧
      combinedTail (Measure.dirac (-1 : ℝ)) 1 = 0 := by
  norm_num [leftTail, rightTail, combinedTail, Measure.dirac_apply]

/-- A positive boundary atom is excluded from the strict right tail. -/
theorem positive_boundary_atom : rightTail (Measure.dirac (1 : ℝ)) 1 = 0 := by
  norm_num [rightTail, Measure.dirac_apply]

/-- The truncated first moment includes its positive upper endpoint atom. -/
theorem first_moment_upper_endpoint_atom :
    (∫ y in Set.Ioc (0 : ℝ) 1, y ∂Measure.dirac (1 : ℝ)) = 1 := by
  rw [MeasureTheory.setIntegral_dirac]
  norm_num

/-- Threshold zero excludes an atom at zero from the absolute strict tail. -/
theorem zero_boundary_atom : combinedTail (Measure.dirac (0 : ℝ)) 0 = 0 := by
  norm_num [leftTail, rightTail, combinedTail, Measure.dirac_apply]

/-- The absolute-tail interpretation needs a nonnegative threshold. -/
theorem negative_threshold_overlap :
    combinedTail (Measure.dirac (0 : ℝ)) (-1) = 2 ∧
      ((Measure.dirac (0 : ℝ)) {y | (-1 : ℝ) < |y|}).toReal = 1 := by
  norm_num [leftTail, rightTail, combinedTail, Measure.dirac_apply]

/-- An eventually empty Dirac tail has no canonical balance parameter. -/
theorem zero_tail_has_no_balance (a p : ℝ) : ¬ HasTailBalance (Measure.dirac a) p :=
  not_hasTailBalance_dirac a p

/-- A factor may be negative early and eventually equal one. -/
noncomputable def earlySignFactor (x : ℝ) : ℝ := if x ≤ 1 then -1 else 1

theorem early_sign_factor_canonical_slow : IsSlowlyVarying earlySignFactor := by
  apply isSlowlyVarying_one.of_eventuallyEq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp [earlySignFactor, not_le_of_gt hx]

theorem early_sign_factor_fails_global_positivity :
    ¬ (∀ x : ℝ, 0 < x → 0 < earlySignFactor x) := by
  intro h
  have h1 := h 1 (by norm_num)
  norm_num [earlySignFactor] at h1

/-- The existential RV property survives early zeros in the represented function. -/
noncomputable def earlyZeroPower (x : ℝ) : ℝ := if x ≤ 1 then 0 else x ^ (-1 : ℝ)

theorem early_zero_power_canonical_rv : IsRegularlyVarying earlyZeroPower (-1) := by
  apply (isRegularlyVarying_rpow (-1)).of_eventuallyEq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp [earlyZeroPower, not_le_of_gt hx]

end MathlibExtTest.Probability.TailIntegralRVCharacterization
