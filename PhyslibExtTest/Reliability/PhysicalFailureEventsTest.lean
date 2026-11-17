/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Reliability.PhysicalFailureEvents

/-!
# Critical crack length checks

Concrete consumers of `PhyslibExt.Reliability.PhysicalFailureEvents`:
the critical length for unit geometry and stress, sharpness at the
threshold, the subcritical zero crack, and the degenerate zero-stress
case showing the positivity hypotheses cannot be dropped.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Unit-parameter threshold
- B. Degenerate stress

## iv. References

- `PhyslibExt.Reliability.PhysicalFailureEvents`
-/

/-- Unit geometry and stress with toughness `2`: `a_c = 4 / π`. -/
example : Reliability.criticalCrackLength 2 1 1 = 4 / Real.pi := by
  unfold Reliability.criticalCrackLength
  norm_num

/-- The critical length for unit parameters is positive. -/
example : 0 < Reliability.criticalCrackLength 2 1 1 :=
  Reliability.criticalCrackLength_pos (by norm_num) one_pos one_pos

/-- At the critical length the intensity reaches the toughness `2`. -/
example :
    Reliability.modeIStressIntensity 1 1
        (Reliability.criticalCrackLength 2 1 1) = 2 :=
  Reliability.modeIStressIntensity_criticalCrackLength
    (by norm_num) one_pos one_pos

/-- Failure is equality-inclusive: the critical length itself fails. -/
example :
    Reliability.crackFailure 2 1 1 (Reliability.criticalCrackLength 2 1 1) :=
  (Reliability.crackFailure_iff_criticalCrackLength_le (by norm_num) one_pos
    one_pos (le_of_lt (Reliability.criticalCrackLength_pos
      (by norm_num) one_pos one_pos))).mpr le_rfl

/-- The zero crack is subcritical and does not fail. -/
example : Reliability.modeIStressIntensity 1 1 0 < 2 ∧
    ¬ Reliability.crackFailure 2 1 1 0 := by
  refine ⟨?_, ?_⟩
  · rw [Reliability.modeIStressIntensity_zero]
    norm_num
  · rw [Reliability.crackFailure_iff_criticalCrackLength_le (by norm_num)
      one_pos one_pos le_rfl]
    exact not_le.mpr (Reliability.criticalCrackLength_pos
      (by norm_num) one_pos one_pos)

/-- Boundary degeneracy: with zero stress the adopted intensity is
identically zero, so the threshold characterization needs its positivity
hypotheses. -/
example (a : ℝ) : Reliability.modeIStressIntensity 1 0 a = 0 := by
  simp [Reliability.modeIStressIntensity]
