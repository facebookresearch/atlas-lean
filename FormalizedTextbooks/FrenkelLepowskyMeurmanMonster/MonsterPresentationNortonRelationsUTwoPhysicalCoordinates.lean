/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact denominator-four physical columns of the squared and inverse-squared Norton actions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoPhysicalData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem product_entry (i j : Fin 24) :
    ∑ k : Fin 24, monsterNortonUNumerator1 i k * monsterNortonUNumerator1 k j =
      4 * monsterNortonUTwoPhysicalNumerator i j := by
  have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℤ => M i j)
    monsterNortonUTwoPhysicalNumerator_certificate
  exact h

/-- The full genuine squared Norton action on each physical delta is its exact integer column. -/
theorem monsterNortonUTwoPhysical_basis (j i : Fin 24) :
    (monsterNortonUFiber.val.2 ^ 2).val (Pi.single j 1) i =
      (monsterNortonUTwoPhysicalNumerator i j : ℝ) / 4 := by
  change monsterNortonUFiber.val.2.val
    (monsterNortonUFiber.val.2.val (Pi.single j 1)) i = _
  rw [monsterNortonUPhysical_vector]
  simp only [monsterNortonUPhysicalMatrix_basis]
  have hs : (∑ k : Fin 24, ((monsterNortonUNumerator1 i k : ℝ) / 4) *
      ((1 / 4 : ℝ) * (monsterNortonUNumerator1 k j : ℝ))) =
      ((∑ k : Fin 24, monsterNortonUNumerator1 i k * monsterNortonUNumerator1 k j : ℤ) : ℝ) /
        16 := by
    simp only [Int.cast_sum, Int.cast_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs, product_entry]
  simp only [Int.cast_mul, Int.cast_ofNat]
  ring

/-- Literal inverse-squared physical columns are the transpose of the actual squared columns. -/
theorem monsterNortonUTwoInversePhysical_basis (j i : Fin 24) :
    ((monsterNortonUFiber.val.2 ^ 2)⁻¹).val (Pi.single j 1) i =
      (monsterNortonUTwoPhysicalNumerator j i : ℝ) / 4 := by
  change (monsterNortonUFiber.val.2 ^ 2).val.symm (Pi.single j 1) i = _
  rw [leechIsom_inverse_coordinate]
  exact monsterNortonUTwoPhysical_basis i j

/-- Every complete real physical vector uses the exact squared numerator. -/
theorem monsterNortonUTwoPhysical_vector (x : Fin 24 → ℝ) (i : Fin 24) :
    (monsterNortonUFiber.val.2 ^ 2).val x i =
      ∑ j : Fin 24, ((monsterNortonUTwoPhysicalNumerator i j : ℝ) / 4) * x j := by
  rw [← leechIsomMatrix_mulVec (monsterNortonUFiber.val.2 ^ 2)]
  simp only [Matrix.mulVec, dotProduct, leechIsomMatrix, monsterNortonUTwoPhysical_basis]

/-- Every inverse-squared vector uses precisely the transpose of this genuine numerator. -/
theorem monsterNortonUTwoInversePhysical_vector (x : Fin 24 → ℝ) (i : Fin 24) :
    ((monsterNortonUFiber.val.2 ^ 2)⁻¹).val x i =
      ∑ j : Fin 24, ((monsterNortonUTwoPhysicalNumerator j i : ℝ) / 4) * x j := by
  rw [← leechIsomMatrix_mulVec ((monsterNortonUFiber.val.2 ^ 2)⁻¹)]
  simp only [Matrix.mulVec, dotProduct, leechIsomMatrix, monsterNortonUTwoInversePhysical_basis]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
