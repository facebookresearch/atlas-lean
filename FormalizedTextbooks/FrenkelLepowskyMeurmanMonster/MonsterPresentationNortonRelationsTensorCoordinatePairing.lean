/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original tensor coordinate reads are exact pairings with genuine physical tensor units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorDictionaryPairings

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem zero_right_dot {I : Type*} [Fintype I] (X : I → ℝ) :
    (∑ r : I, X r * (0 : I → ℝ) r) = 0 := by
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem tensor_unit_pairing {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (T : I → J → ℝ) (t : I) (i : J) :
    (∑ u : I, ∑ j : J, T u j *
      (if j = i then (Pi.single t 1 : I → ℝ) u else 0)) = T t i := by
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- Pairing with one genuine physical tensor unit reads exactly its original tensor coordinate. -/
theorem monsterNortonForm_tensorUnit_right (x : GriessSpace) (t : SpinIndex) (i : Fin 24) :
    griessForm x (monsterNortonTensorUnit t i) = (griessConwayEncode x).2.2 t i := by
  rw [griessForm_eq_conwayRawForm, monsterNortonTensorUnit, monsterNortonTensorLift_apply,
    griessConwayEncode_decode _ (by intros; rfl), conwayRawForm, zero_right_dot]
  simp only [conwayMatrixForm_eq_sum, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    zero_add, add_zero]
  exact tensor_unit_pairing (I := SpinIndex) (J := Fin 24)
    (griessConwayEncode x).2.2 t i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
