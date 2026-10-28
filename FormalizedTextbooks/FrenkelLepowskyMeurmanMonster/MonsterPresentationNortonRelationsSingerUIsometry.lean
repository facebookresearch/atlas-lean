/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Singer Leech isometry intertwines literal Norton U with its cube. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerULattice

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem action_power (e : leechIsomSubgroup)
    (A : Matrix (Fin 24) (Fin 24) ℝ)
    (h : ∀ x : Fin 24 → ℝ, e.val x = A *ᵥ x) (n : ℕ) (x : Fin 24 → ℝ) :
    (e ^ n).val x = (A ^ n) *ᵥ x := by
  induction n generalizing x with
  | zero => simp
  | succ n hn =>
    change ((e ^ n) * e).val x = _
    change (e ^ n).val (e.val x) = _
    rw [hn, h, Matrix.mulVec_mulVec, ← pow_succ]

/-- The rational physical permutation matrix gives its genuine action on real coordinates. -/
theorem monsterNortonSingerPermutation_real_matrix (x : Fin 24 → ℝ) :
    (monsterNortonSingerPermutationIsometry 0).val x =
      ((monsterNortonSingerPhysicalMatrix.map (Int.castRingHom ℚ)).map
        (Rat.castHom ℝ)) *ᵥ x := by
  ext i
  simp [monsterNortonSingerPermutationIsometry, golayPermutationIsometry,
    golayRealPermute_apply, monsterNortonSingerPhysicalMatrix,
    Matrix.mulVec, dotProduct, monsterNortonSingerGolayPermutation,
    monsterNortonSingerPermutation, apply_ite, ite_mul]

/-- The actual lattice isometries satisfy the exact Singer intertwining relation. -/
theorem monsterNortonSinger_U_leech_intertwines :
    monsterNortonSingerPermutationIsometry 0 * monsterNortonUFiber.val.2 =
      monsterNortonUFiber.val.2 ^ 3 * monsterNortonSingerPermutationIsometry 0 := by
  have h := congrArg (Rat.castHom ℝ).mapMatrix monsterNortonSingerU_matrix_intertwines
  rw [map_mul, map_mul, map_pow] at h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (monsterNortonSingerPermutationIsometry 0).val
    (monsterNortonUFiber.val.2.val x) =
      (monsterNortonUFiber.val.2 ^ 3).val
        ((monsterNortonSingerPermutationIsometry 0).val x)
  rw [monsterNortonSingerPermutation_real_matrix, monsterNortonUFiber_leech_matrix,
    action_power _ _ monsterNortonUFiber_leech_matrix,
    monsterNortonSingerPermutation_real_matrix, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  exact congrArg (fun M => M *ᵥ x) h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
