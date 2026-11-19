/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.TrussCompatibility
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Truss-compatibility checks

Concrete consumers of
`PhyslibExt.Mechanics.TrussCompatibility` on a three-joint
table: horizontal-member elongation pairing, supported
energy value, and a zero-length member contributing a zero
unit row.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Row action and supported energy

## iv. References

- `PhyslibExt.Mechanics.TrussCompatibility`
-/

open Matrix
open PhyslibExt.Mechanics.HarmonicMechanics
open Mechanics.TrussCompatibility

namespace PhyslibExtTest.Mechanics.TrussCompatibility

/-- Joints at `(0,0)`, `(4,0)`, `(1,3)`; one member 0 → 1. -/
private abbrev r3 : Fin 3 → (Fin 2 → ℝ) := ![![0, 0], ![4, 0], ![1, 3]]

/-- Joint displacement: `(1, 0)` at joint 0, `(3, 0)` at
joint 1, zero else. -/
private def u6 : Fin 3 × Fin 2 → ℝ :=
  fun q => if q = (0, 0) then 1 else if q = (1, 0) then 3 else 0

/-- Identity injection on joint coordinates. -/
private abbrev S6 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ := 1

/-! ## A. Row action and supported energy -/

/-- Horizontal member of length 4: the separation row reads
`4 * (3 - 1) = 8` (separation pairing, `L` times elongation). -/
example : (axialCompatibility r3 ![0] ![1] *ᵥ u6) 0 = 8 := by
  rw [axialCompatibility_mulVec_apply]
  norm_num [Fin.sum_univ_two, u6]

/-- The unit row reads the elongation `2`. -/
example : (axialCompatibilityUnit r3 ![0] ![1] *ᵥ u6) 0 = 2 := by
  have hL : memberLength r3 ![0] ![1] 0 = 4 := by
    rw [memberLength]
    norm_num
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hrow : axialCompatibilityUnit r3 ![0] ![1]
      = (4 : ℝ)⁻¹ • axialCompatibility r3 ![0] ![1] := by
    ext e q
    fin_cases e <;> simp [axialCompatibilityUnit, hL]
  rw [hrow, Matrix.smul_mulVec]
  have h8 : (axialCompatibility r3 ![0] ![1] *ᵥ u6) 0 = 8 := by
    rw [axialCompatibility_mulVec_apply]
    norm_num [Fin.sum_univ_two, u6]
  simp [h8]
  norm_num

/-- Supported energy with the identity injection and unit
stiffness: `1 * 8 ^ 2 = 64` in separation form. -/
example : u6 ⬝ᵥ (((axialCompatibility r3 ![0] ![1] * S6)ᵀ
          * Matrix.diagonal (![1] : Fin 1 → ℝ)
          * (axialCompatibility r3 ![0] ![1] * S6)) *ᵥ u6)
    = 64 := by
  rw [supported_quad_form_eq_sum]
  simp only [Matrix.mulVec_apply, Matrix.row, dotProduct,
    axialCompatibility, Matrix.of_apply, u6, Fintype.sum_prod_type, Finset.univ_product_univ,
    Finset.sum_product, Fin.sum_univ_three, Fin.sum_univ_two]
  norm_num

/-- A zero-length member contributes a zero unit row. -/
example : (axialCompatibilityUnit (![![1, 1], ![1, 1]] :
        Fin 2 → (Fin 2 → ℝ)) ![0] ![1]
      *ᵥ fun q => if q = (0, 0) then 1 else 0) 0 = 0 := by
  rw [Matrix.mulVec_apply]
  simp [axialCompatibilityUnit, axialCompatibility, memberLength,
    dotProduct, Fin.sum_univ_two]

/-- Positive semidefiniteness client at unit data. -/
example : ((axialCompatibility r3 ![0] ![1] * S6)ᵀ
    * Matrix.diagonal (![1] : Fin 1 → ℝ)
    * (axialCompatibility r3 ![0] ![1] * S6)).PosSemidef :=
  supported_posSemidef r3 ![0] ![1] S6 (![1] : Fin 1 → ℝ)
    (by intro i; fin_cases i <;> norm_num)

#print axioms
  Mechanics.TrussCompatibility.axialCompatibility_mulVec_apply
#print axioms
  Mechanics.TrussCompatibility.axialCompatibility_transpose_mulVec_apply
#print axioms
  Mechanics.TrussCompatibility.axialCompatibilityUnit_transpose_mulVec_apply
#print axioms Mechanics.TrussCompatibility.supported_quad_form_eq_sum
#print axioms Mechanics.TrussCompatibility.supported_posSemidef

end PhyslibExtTest.Mechanics.TrussCompatibility
