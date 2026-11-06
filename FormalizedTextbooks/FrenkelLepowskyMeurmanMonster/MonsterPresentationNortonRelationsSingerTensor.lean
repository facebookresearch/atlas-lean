/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Singer lift acts on the genuine tensor constituent by two coordinate permutations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationLocalTensorFaithfulness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The actual fiber tensor action is its explicit spin and physical coordinate relabeling. -/
theorem monsterNortonSinger_tensor_apply (X : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation monsterNortonSingerFiber X t i =
      X ((monsterNortonSingerCode 0).symm t) ((monsterNortonSingerPermutation 0).symm i) := by
  obtain ⟨x, rfl⟩ := conwayTensorCoordinates.surjective X
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [localTensorRepresentation_coordinates]
    change conwayTensorCoordinates
      (monsterNortonSingerSpin.val a ⊗ₜ[ℝ]
        (monsterNortonSingerPermutationIsometry 0).val b) t i = _
    simp only [conwayTensorCoordinates_tmul]
    rfl
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]

/-- The coordinate formula belongs to the actual Griess action of the local quotient lift. -/
theorem monsterNortonSingerLocal_tensor (x : GriessSpace) (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal monsterNortonSingerLocal x)).2.2 t i =
      (griessConwayEncode x).2.2 ((monsterNortonSingerCode 0).symm t)
        ((monsterNortonSingerPermutation 0).symm i) := by
  rw [monsterLocalTensor_encode]
  exact monsterNortonSinger_tensor_apply _ t i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
