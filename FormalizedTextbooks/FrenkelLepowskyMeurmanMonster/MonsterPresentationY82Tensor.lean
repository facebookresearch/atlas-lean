/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine tensor action of the explicit source y82 spin/Leech pair. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82ABC

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine code isometry multiplies each physical coordinate by its source sign. -/
theorem monsterSourceY82_physical_apply (b : Fin 24 → ℝ) (i : Fin 24) :
    monsterSourceY82Isometry.val b i =
      qSign (golayEncoder monsterSourceY82Code i) * b i := by
  simp [monsterSourceY82Isometry, golaySignIsometry, golayRealSign_apply,
    monsterSourceY82SignCode]

/-- The actual tensor representation applies the proved spin operator in each signed column. -/
theorem monsterSourceY82_tensor (x : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation monsterSourceY82Fiber x t i =
      qSign (golayEncoder monsterSourceY82Code i) *
        monsterSourceY82Spin.val (fun u => x u i) t := by
  obtain ⟨v, rfl⟩ := conwayTensorCoordinates.surjective x
  rw [localTensorRepresentation_coordinates]
  induction v using TensorProduct.inductionOn with
  | tmul a b =>
    change conwayTensorCoordinates (TensorProduct.congr _ _ (a ⊗ₜ[ℝ] b)) t i = _
    rw [TensorProduct.congr_tmul, conwayTensorCoordinates_tmul]
    simp only [conwayTensorCoordinates_tmul]
    change monsterSourceY82Spin.val a t * monsterSourceY82Isometry.val b i = _
    rw [monsterSourceY82_physical_apply]
    have hab : (fun u => a u * b i) = b i • a := by
      funext u
      exact mul_comm _ _
    rw [hab]
    rw [map_smul]
    change _ = qSign (golayEncoder monsterSourceY82Code i) *
      (b i * monsterSourceY82Spin.val a t)
    ring
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply, ha, hb]
    change _ = qSign (golayEncoder monsterSourceY82Code i) *
      (monsterSourceY82Spin.val ((fun u => conwayTensorCoordinates a u i) +
        (fun u => conwayTensorCoordinates b u i)) t)
    rw [map_add]
    simp only [Pi.add_apply, mul_add]

/-- The candidate's encoded spin tensor is its actual column spin action. -/
theorem monsterSourceY82_encode_tensor (x : GriessSpace) (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal monsterSourceY82Local x)).2.2 t i =
      qSign (golayEncoder monsterSourceY82Code i) *
        monsterSourceY82Spin.val (fun u => (griessConwayEncode x).2.2 u i) t := by
  rw [show rhoLocal monsterSourceY82Local =
    localGriessRepresentation monsterSourceY82Fiber from rfl,
    localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  exact monsterSourceY82_tensor (griessConwayEncode x).2.2 t i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
