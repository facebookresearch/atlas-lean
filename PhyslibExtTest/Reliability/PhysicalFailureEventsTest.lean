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

/-- Paris power branch at `m = 3` (so `r = -1/2`), `K = 1`, `a0 = 1`:
the crack reaches `ac = 2` at its positive life, and the life precedes
the blow-up count `2`. -/
example : 0 < Reliability.parisLifePow (-1/2) 1 1 2 ∧
    Reliability.parisCrackPow (-1/2) 1 1
        (Reliability.parisLifePow (-1/2) 1 1 2) = 2 ∧
      Reliability.parisLifePow (-1/2) 1 1 2 <
        (1:ℝ) ^ (-1/2:ℝ) / (-((-1/2) * 1)) :=
  ⟨Reliability.parisLifePow_pos (by norm_num) one_pos (by norm_num)
      (by norm_num),
    Reliability.parisCrackPow_at_life (by norm_num) one_pos (by norm_num)
      (by norm_num),
    Reliability.parisLifePow_lt_blowup (by norm_num) one_pos (by norm_num)
      (by norm_num)⟩

/-- Paris logarithmic branch at `K = 1`, `a0 = 1`: the crack reaches
`ac = 2` at `log 2`. -/
example : Reliability.parisCrackExp 1 1 (Reliability.parisLifeExp 1 1 2) = 2 :=
  Reliability.parisCrackExp_at_life (by norm_num) one_pos (by norm_num)

/-- Paris derivative API at the negative-`r` point `N = 1`
(`r = -1/2`, `K = 1`, `a0 = 1`; base `1 - 1/2 = 1/2 > 0`). -/
example :
    HasDerivAt (Reliability.parisCrackPow (-1/2) 1 1)
      (1 * (Reliability.parisCrackPow (-1/2) 1 1 1) ^ ((1 - (-1/2 : ℝ)) : ℝ)) 1 :=
  Reliability.hasDerivAt_parisCrackPow (r := -1/2) (K := 1) (a0 := 1)
    (N := 1) (by norm_num)
    (by rw [Real.one_rpow]; norm_num)

/-- Paris logarithmic derivative API at `N = 0`. -/
example :
    HasDerivAt (Reliability.parisCrackExp 1 1)
      (1 * Reliability.parisCrackExp 1 1 0) 0 :=
  Reliability.hasDerivAt_parisCrackExp 1 1 0

/-- Power-branch first crossing at `N = 0`: crack `1` is below
`ac = 2`, using the positive life. -/
example : Reliability.parisCrackPow (-1/2) 1 1 0 < 2 :=
  (Reliability.parisCrackPow_lt_iff (r := -1/2) (K := 1) (a0 := 1)
    (ac := 2) (N := 0) (by norm_num) one_pos (by norm_num) (by norm_num)
    (by rw [Real.one_rpow]; norm_num)).mpr
    (Reliability.parisLifePow_pos (r := -1/2) (K := 1) (a0 := 1) (ac := 2)
      (by norm_num) one_pos (by norm_num) (by norm_num))

/-- Log-branch first crossing at `N = 0`. -/
example : Reliability.parisCrackExp 1 1 0 < 2 :=
  (Reliability.parisCrackExp_lt_iff (K := 1) (a0 := 1) (ac := 2) (N := 0)
    (by norm_num) one_pos (by norm_num)).mpr
    (Reliability.parisLifeExp_pos (K := 1) (a0 := 1) (ac := 2)
      (by norm_num) one_pos (by norm_num))
