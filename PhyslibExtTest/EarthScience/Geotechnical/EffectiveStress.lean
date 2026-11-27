/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.EffectiveStress
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Effective-stress conversion checks

Concrete consumers of
`PhyslibExt.EarthScience.Geotechnical.EffectiveStress`:
hydrostatic total stress in both conventions, normal
reversal, and zero pore pressure.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Hydrostatic and reversal checks

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.EffectiveStress`
-/

open Matrix
open Elasticity
open EarthScience

namespace PhyslibExtTest.EarthScience.Geotechnical.EffectiveStress

/-! ## A. Hydrostatic and reversal checks -/

/-- Hydrostatic tension-positive total stress `-3 • 1` with
pore pressure `2`: effective stress is `-1 • 1`. -/
example : effectiveStressTensionPositive
      (((-3 : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 2
    = (-1) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [effectiveStressTensionPositive, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] <;> norm_num

/-- Round trip through the compression-positive formula. -/
example : compressionPositiveStress
      (effectiveStressCompressionPositive
        (compressionPositiveStress
          (((-3 : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) 2)
    = (-1) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [effectiveStress_roundTrip]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [effectiveStressTensionPositive, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] <;> norm_num

/-- Effective traction on a unit normal. -/
example : compressionPositiveTraction
      (effectiveStressCompressionPositive
        (compressionPositiveStress
          (((-3 : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) 2) ![1, 0]
    = ![-1, 0] := by
  rw [effectiveStress_traction]
  ext i
  fin_cases i <;> simp [traction, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] <;> norm_num

/-- Effective traction on the reversed normal flips sign. -/
example : compressionPositiveTraction
      (effectiveStressCompressionPositive
        (compressionPositiveStress
          (((-3 : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) 2) (-![1, 0])
    = ![1, 0] := by
  rw [effectiveStress_traction]
  ext i
  fin_cases i <;> simp [traction, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] <;> norm_num

/-- Zero pore pressure reduces to total stress. -/
example : effectiveStressTensionPositive
      (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ) 0
    = !![2, 1; 1, 3] :=
  (effectiveStress_zero_pore_pressure _).2

/-- Wrong-sign control: the tension-positive formula is not
a subtraction. -/
example : effectiveStressTensionPositive
      (0 : Matrix (Fin 2) (Fin 2) ℝ) 2
    ≠ (-2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [effectiveStressTensionPositive] at h00
  norm_num at h00

#print axioms EarthScience.effectiveStress_conversion
#print axioms EarthScience.effectiveStress_roundTrip
#print axioms EarthScience.effectiveStress_traction

end PhyslibExtTest.EarthScience.Geotechnical.EffectiveStress
