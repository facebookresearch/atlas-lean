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
energy value, a zero-length member contributing a zero
unit row, and supported virtual work on the mechanism
(one-member) truss.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Row action and supported energy
- B. Supported virtual work

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

/-- Supported quadratic form (twice linearized stored energy)
with the identity injection and unit stiffness:
`1 * 8 ^ 2 = 64` in separation form. -/
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

/-! ## B. Supported virtual work -/

/-- Supported load balanced by `s = 2` on the one-member
table: `-8` at joint 0 `x`, `8` at joint 1 `x`. -/
private def fB : Fin 3 × Fin 2 → ℝ :=
  fun q => if q = (0, 0) then -8 else if q = (1, 0) then 8 else 0

/-- The balanced-load identity `(B * 1)ᵀ *ᵥ ![2] = fB`,
coordinate by coordinate. -/
example : (axialCompatibility r3 ![0] ![1] * S6)ᵀ *ᵥ (![2] : Fin 1 → ℝ)
    = fB := by
  funext q
  obtain ⟨j, k⟩ := q
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.mulVec_apply, Matrix.transpose_apply, axialCompatibility,
      Matrix.of_apply, dotProduct, fB, r3] <;> norm_num

/-- Forward direction at the nonzero virtual displacement
`u6`: internal and external virtual work are both `16`.
The one-member table is a mechanism (its compatibility map
has a large kernel); no injectivity is needed. -/
example : (![2] : Fin 1 → ℝ)
      ⬝ᵥ ((axialCompatibility r3 ![0] ![1] * S6) *ᵥ u6) = fB ⬝ᵥ u6 ∧
    fB ⬝ᵥ u6 = 16 := by
  have heq : (axialCompatibility r3 ![0] ![1] * S6)ᵀ *ᵥ (![2] : Fin 1 → ℝ)
      = fB := by
    funext q
    obtain ⟨j, k⟩ := q
    fin_cases j <;> fin_cases k <;>
      simp [Matrix.mulVec_apply, Matrix.transpose_apply, axialCompatibility,
        Matrix.of_apply, dotProduct, fB, r3] <;> norm_num
  refine ⟨(supported_virtualWork_iff r3 ![0] ![1] S6 _ _).mp heq u6, ?_⟩
  simp only [dotProduct, u6, fB, Fintype.sum_prod_type, Fin.sum_univ_three,
    Fin.sum_univ_two]
  norm_num

/-- Reverse direction at the zero support map: virtual
work (both sides zero) gives the zero equilibrium. -/
example (s : Fin 1 → ℝ) :
    (axialCompatibility r3 ![0] ![1] * (0 : Matrix (Fin 3 × Fin 2)
        (Fin 3 × Fin 2) ℝ))ᵀ *ᵥ s = 0 :=
  (supported_virtualWork_iff r3 ![0] ![1] 0 s 0).mpr (fun v => by simp)

/-- Mechanism negative control: a transverse load at joint
0 cannot be balanced by any member coefficient, because
the transverse virtual displacement does no internal work. -/
example (s : Fin 1 → ℝ) :
    ¬ ∀ v : Fin 3 × Fin 2 → ℝ,
      s ⬝ᵥ ((axialCompatibility r3 ![0] ![1] * S6) *ᵥ v)
        = (fun q => if q = (0, 1) then (1 : ℝ) else 0) ⬝ᵥ v := by
  intro h
  have hv := h (fun q => if q = (0, 1) then (1 : ℝ) else 0)
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three,
    Fin.sum_univ_two, Fin.sum_univ_one, Matrix.mulVec_apply, Matrix.row,
    axialCompatibility, Matrix.of_apply, Matrix.one_apply,
    Matrix.mul_apply] at hv
  norm_num [r3] at hv

#print axioms
  Mechanics.TrussCompatibility.axialCompatibility_mulVec_apply
#print axioms
  Mechanics.TrussCompatibility.axialCompatibility_transpose_mulVec_apply
#print axioms
  Mechanics.TrussCompatibility.axialCompatibilityUnit_transpose_mulVec_apply
#print axioms Mechanics.TrussCompatibility.supported_quad_form_eq_sum
#print axioms Mechanics.TrussCompatibility.supported_posSemidef
#print axioms Mechanics.TrussCompatibility.supported_virtualWork_iff

end PhyslibExtTest.Mechanics.TrussCompatibility
