/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2Co1Stabilizer

/-! The actual real-plane and short-line flag action and stabilizer transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine Conway isometries act on real planes by their original linear maps. -/
instance : MulAction leechIsomSubgroup (Submodule ℝ (Fin 24 → ℝ)) where
  smul g p := p.map g.val.toLinearMap
  one_smul p := by
    change p.map LinearMap.id = p
    exact Submodule.map_id _
  mul_smul g h p := by
    change p.map (g * h).val.toLinearMap = (p.map h.val.toLinearMap).map g.val.toLinearMap
    rw [← Submodule.map_comp]
    rfl

/-- The original rooted flag subgroup fixes precisely its actual real plane and label. -/
theorem leechRootedA2FlagStabilizer_eq_stabilizer (p : leechRootedA2Plane) :
    leechRootedA2FlagStabilizer p =
      MulAction.stabilizer leechIsomSubgroup (p.val, leechRootedA2RootAddress) := by
  ext e
  rw [leechRootedA2FlagStabilizer_mem]
  change _ ↔ e • (p.val, leechRootedA2RootAddress) = (p.val, leechRootedA2RootAddress)
  rw [Prod.ext_iff]
  change _ ↔ p.val.map e.val.toLinearMap = p.val ∧
    griessShortPermutation e leechRootedA2RootAddress = leechRootedA2RootAddress
  rw [leechRootedA2_short_perm_eq_iff, leechRootedA2RootAddress_integral]
  exact and_comm

/-- The actual global action stabilizer of a standard-root plane flag has its counted order. -/
theorem leechRootedA2Flag_action_stabilizer_card (p : leechRootedA2Plane) :
    Nat.card (MulAction.stabilizer leechIsomSubgroup (p.val, leechRootedA2RootAddress)) =
      36787322880 := by
  rw [← leechRootedA2FlagStabilizer_eq_stabilizer, leechRootedA2FlagStabilizer_card]

/-- Transport to a genuine standard-root flag preserves the actual flag stabilizer order. -/
theorem leechRootedA2Flag_stabilizer_card_of_transport
    (S : Submodule ℝ (Fin 24 → ℝ)) (r : GriessShortIndex) (p : leechRootedA2Plane)
    (e : leechIsomSubgroup) (he : e • (S, r) = (p.val, leechRootedA2RootAddress)) :
    Nat.card (MulAction.stabilizer leechIsomSubgroup (S, r)) = 36787322880 := by
  calc
    _ = Nat.card (MulAction.stabilizer leechIsomSubgroup (p.val, leechRootedA2RootAddress)) :=
      Nat.card_congr (MulAction.stabilizerEquivStabilizer he.symm).toEquiv
    _ = _ := leechRootedA2Flag_action_stabilizer_card p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
