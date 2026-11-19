/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.SpaceTrajectoryModels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Thrust-only rendezvous checks

Concrete consumers of `PhyslibExt.Mechanics.SpaceTrajectoryModels`: the nonzero burn, with its
displacement `1 - log 2` and final speed `log 2`; the mid-burn thrust; and the depletion time
`t = 2`, outside the burn interval, where the velocity formula takes a junk value.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. The burn and the depletion boundary

## iv. References

- `PhyslibExt.Mechanics.SpaceTrajectoryModels`
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.SpaceTrajectoryModels

open Set PhyslibExt.Mechanics.SpaceTrajectoryModels

/-! ## A. The burn and the depletion boundary -/

/-- Nonzero burn: the mass falls from `2` to `1`; the displacement `x 1 - x 0 = ∫₀¹ v` is
`1 - log 2` (about `0.307`) and the final speed is `log 2` (about `0.693`), both positive. -/
example :
    burnMass 1 < burnMass 0 ∧ burnPosition 1 - burnPosition 0 = 1 - Real.log 2 ∧
      ∫ t in (0 : ℝ)..1, burnVelocity t = 1 - Real.log 2 ∧ 0 < 1 - Real.log 2 ∧
      burnVelocity 1 = Real.log 2 ∧ 0 < Real.log 2 := by
  have hm10 : burnMass 1 < burnMass 0 := by unfold burnMass; norm_num
  have hx : burnPosition 1 - burnPosition 0 = 1 - Real.log 2 := by
    have hx0 := (burn_initial).1
    have hr := rendezvous.1
    have ht1 : targetPosition 1 = 1 - Real.log 2 := by unfold targetPosition; ring
    have hx1 : burnPosition 1 = 1 - Real.log 2 := hr.trans ht1
    rw [hx1, hx0, sub_zero]
  have hint_eq : ∫ t in (0 : ℝ)..1, burnVelocity t = 1 - Real.log 2 := by
    rw [←burnPosition_sub_eq_integral]
    exact hx
  have hlog2_lt : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
    linarith
  have hpos1 : (0 : ℝ) < 1 - Real.log 2 := by linarith
  have hv1 : burnVelocity 1 = Real.log 2 := rendezvous.2.1
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  exact ⟨hm10, hx, hint_eq, hpos1, hv1, hlog2_pos⟩

/-- Fuel depletion: the mass vanishes at `t = 2`, which lies outside the burn interval `[0, 1]`.
There the velocity formula is outside the model: Lean's `2 / 0 = 0` and `log 0 = 0` give the junk
value `burnVelocity 2 = 0`, not a terminal speed. -/
example :
    burnMass 2 = 0 ∧ (2 : ℝ) ∉ Icc (0 : ℝ) 1 ∧ burnVelocity 2 = 0 := by
  have hm2 : burnMass 2 = 0 := by unfold burnMass; norm_num
  have hmem : (2 : ℝ) ∉ Icc (0 : ℝ) 1 := by
    intro h
    rw [mem_Icc] at h
    norm_num at h
  have hv2 : burnVelocity 2 = 0 := by
    unfold burnVelocity
    have h0 : (2 : ℝ) / ((2 : ℝ) - 2) = 0 := by
      have h22 : (2 : ℝ) - 2 = 0 := by norm_num
      rw [h22, div_zero]
    rw [h0, Real.log_zero]
  exact ⟨hm2, hmem, hv2⟩

/-- Mid-burn, `t = 1 / 2`: the mass is `3 / 2`, the velocity rate is `v' = 1 / (2 - t) = 2 / 3`,
and the law gives the thrust `m v' = 1`. -/
example :
    burnMass (1 / 2) = 3 / 2 ∧ HasDerivAt burnVelocity (2 / 3) (1 / 2) ∧
      burnMass (1 / 2) * (1 / (2 - 1 / 2)) = 1 := by
  have hv := hasDerivAt_burnVelocity (t := 1 / 2) (by norm_num)
  refine ⟨by norm_num [burnMass], ?_, (burn_law ⟨by norm_num, by norm_num⟩).2⟩
  convert hv using 1
  norm_num

end PhyslibExtTest.Mechanics.SpaceTrajectoryModels
