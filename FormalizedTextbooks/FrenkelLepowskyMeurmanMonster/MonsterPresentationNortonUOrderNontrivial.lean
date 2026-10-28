/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A nonzero off-diagonal entry distinguishes the actual Norton word from the identity. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem matrix_entry_zero_one :
    monsterNortonUMatrixQ.map (Rat.castHom ℝ) 0 1 = (1 / 4 : ℝ) := by
  norm_num [monsterNortonUMatrixQ, monsterNortonUNumerator1]

/-- The local quotient word is nonidentity because its physical matrix is not scalar. -/
theorem monsterNortonULocal_ne_one : monsterNortonULocal ≠ 1 := by
  intro h
  have hd : monsterNortonUFiber ∈ localDiagonalSubgroup :=
    (QuotientGroup.eq_one_iff monsterNortonUFiber).mp h
  rcases hd with ⟨c, _, hc⟩
  have hx := congrFun (hc (Pi.single (1 : Fin 24) (1 : ℝ))) 0
  rw [monsterNortonUFiber_leech_matrix] at hx
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply] at hx
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Pi.smul_apply, Pi.single_eq_of_ne (show (0 : Fin 24) ≠ 1 by decide),
    smul_zero] at hx
  rw [matrix_entry_zero_one] at hx
  norm_num at hx

/-- The literal Norton word is nonidentity in the actual generated group. -/
theorem y555NortonActualU_ne_one : y555NortonActualU ≠ 1 := by
  intro h
  apply monsterNortonULocal_ne_one
  apply localIntoGenerated_injective
  rw [monsterNortonULocal_generated, h, map_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
