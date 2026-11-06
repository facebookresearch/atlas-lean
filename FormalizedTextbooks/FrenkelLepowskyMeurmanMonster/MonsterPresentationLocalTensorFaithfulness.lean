/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual simultaneous-sign quotient is determined by its genuine tensor constituent. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82TensorComparison
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The fiber tensor representation has exactly the simultaneous-sign kernel. -/
theorem monsterLocalTensor_kernel (f : localFiberSubgroup) :
    localTensorRepresentation f = 1 ↔ f ∈ localDiagonalSubgroup := by
  constructor
  · intro hf
    apply (localTensorAction_eq_one_iff f).mp
    apply coordinateGLTransport_injective conwayTensorCoordinates
    change localTensorRepresentation f = coordinateGLTransport conwayTensorCoordinates 1
    rw [hf, map_one]
  · exact localTensorRepresentation_diagonal f

/-- The genuine tensor constituent descends to the actual local group H. -/
noncomputable def monsterLocalTensorRepresentation : H →*
    ((SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ)) :=
  QuotientGroup.lift localDiagonalSubgroup localTensorRepresentation
    (by intro f hf; exact localTensorRepresentation_diagonal f hf)

/-- The descended tensor constituent is faithful on the actual local quotient. -/
theorem monsterLocalTensorRepresentation_injective :
    Function.Injective monsterLocalTensorRepresentation := by
  apply (MonoidHom.ker_eq_bot_iff monsterLocalTensorRepresentation).mp
  ext h
  change monsterLocalTensorRepresentation h = 1 ↔ h = 1
  induction h using QuotientGroup.induction_on with
  | H f =>
    change localTensorRepresentation f = 1 ↔
      QuotientGroup.mk f = (1 : localFiberSubgroup ⧸ localDiagonalSubgroup)
    rw [QuotientGroup.eq_one_iff]
    exact monsterLocalTensor_kernel f

/-- The quotient constituent agrees with the actual encoded Griess action for every input. -/
theorem monsterLocalTensor_encode (h : H) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal h x)).2.2 =
      monsterLocalTensorRepresentation h (griessConwayEncode x).2.2 := by
  induction h using QuotientGroup.induction_on with
  | H f =>
    change (griessConwayEncode (localGriessRepresentation f x)).2.2 =
      localTensorRepresentation f (griessConwayEncode x).2.2
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_tensor]

/-- Equality of encoded tensor actions on every Griess input identifies actual local elements. -/
theorem monsterLocalTensor_identifies (h k : H)
    (he : ∀ x : GriessSpace,
      (griessConwayEncode (rhoLocal h x)).2.2 =
        (griessConwayEncode (rhoLocal k x)).2.2) : h = k := by
  apply monsterLocalTensorRepresentation_injective
  apply LinearEquiv.ext
  intro T
  have ht := he (griessConwayDecode (0, (0, T)))
  rw [monsterLocalTensor_encode, monsterLocalTensor_encode,
    griessConwayEncode_decode _ (by intro i j; rfl)] at ht
  exact ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
