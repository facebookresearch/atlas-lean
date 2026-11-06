/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2RootStabilizer

/-! The actual positive-root stabilizer, obtained from the two orientations of its root line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine integral Conway isometries act on actual integral Leech vectors. -/
instance leechIntegralIsometryMulAction : MulAction leechIsomSubgroup leechIntegral :=
  MulAction.compHom leechIntegral leechIntegralAction

/-- The integral action is the original lattice isometry action. -/
theorem leechIntegral_smul_eq (e : leechIsomSubgroup) (u : leechIntegral) :
    e • u = leechIntegralAction e u := rfl

/-- The original all-ones Golay codeword. -/
def leechRootNegationCode : golayCode := golayCodeLabelEquiv 2048

/-- Every coordinate of the original all-ones codeword is one. -/
theorem leechRootNegationCode_val (i : Fin 24) : leechRootNegationCode.val i = 1 := by
  unfold leechRootNegationCode
  rw [golayCodeLabelEquiv_val]
  revert i
  decide +kernel

/-- The all-ones Golay sign isometry is actual negation of every lattice vector. -/
theorem leechRootNegationCode_action (u : leechIntegral) :
    leechIntegralAction (golaySignIsometry leechRootNegationCode) u = -u := by
  apply Subtype.ext
  rw [leechIntegralAction_golaySign]
  funext i
  simp [golayIntegerSign, leechRootNegationCode_val]

/-- Actual central negation belongs to the root-line stabilizer. -/
def leechRootLineNegation : leechRootedA2RootLineSubgroup :=
  ⟨golaySignIsometry leechRootNegationCode,
    (leechRootedA2RootLineSubgroup_mem _).mpr
      (Or.inr (leechRootNegationCode_action _))⟩

/-- The two orientations of the standard root are distinct integral vectors. -/
theorem leechRootedA2Root_ne_neg : leechRootedA2Root ≠ -leechRootedA2Root := by
  intro h
  have h0 := congrArg (fun u : leechIntegral => u.val (0 : Fin 24)) h
  norm_num [leechRootedA2Root, leechRootedA2RootIntegral] at h0

/-- The root-line stabilizer has exactly the two genuine orientations in its root orbit. -/
theorem leechRootedA2RootLine_orbit :
    MulAction.orbit leechRootedA2RootLineSubgroup leechRootedA2Root =
      {leechRootedA2Root, -leechRootedA2Root} := by
  ext u
  constructor
  · rintro ⟨e, rfl⟩
    rcases (leechRootedA2RootLineSubgroup_mem e.val).mp e.property with h | h
    · apply Set.mem_insert_iff.mpr
      left
      exact h
    · apply Set.mem_insert_iff.mpr
      right
      exact Set.mem_singleton_iff.mpr h
  · intro h
    rcases Set.mem_insert_iff.mp h with h | h
    · subst u
      exact ⟨1, one_smul _ _⟩
    · have hu := Set.mem_singleton_iff.mp h
      subst u
      exact ⟨leechRootLineNegation, leechRootNegationCode_action _⟩

/-- The genuine positive-root stabilizer inside the actual root-line stabilizer. -/
def leechRootedA2PositiveRootSubgroup : Subgroup leechRootedA2RootLineSubgroup :=
  MulAction.stabilizer leechRootedA2RootLineSubgroup leechRootedA2Root

/-- There are precisely two vectors in the actual oriented-root orbit. -/
theorem leechRootedA2RootLine_orbit_card :
    Nat.card (MulAction.orbit leechRootedA2RootLineSubgroup leechRootedA2Root) = 2 := by
  rw [leechRootedA2RootLine_orbit, Nat.card_coe_set_eq,
    Set.ncard_pair leechRootedA2Root_ne_neg]

/-- The actual positive-root stabilizer has the Conway two order. -/
theorem leechRootedA2PositiveRootSubgroup_card :
    Nat.card leechRootedA2PositiveRootSubgroup = 42305421312000 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite leechRootedA2RootLineSubgroup
  let : Finite (MulAction.orbit leechRootedA2RootLineSubgroup leechRootedA2Root) :=
    (Finite.finite_mulAction_orbit leechRootedA2Root).to_subtype
  let _ := Fintype.ofFinite
    (MulAction.orbit leechRootedA2RootLineSubgroup leechRootedA2Root)
  let _ := Fintype.ofFinite leechRootedA2PositiveRootSubgroup
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    leechRootedA2RootLineSubgroup leechRootedA2Root
  simp only [← Nat.card_eq_fintype_card] at h
  change Nat.card (MulAction.orbit leechRootedA2RootLineSubgroup leechRootedA2Root) *
    Nat.card leechRootedA2PositiveRootSubgroup = Nat.card leechRootedA2RootLineSubgroup at h
  rw [leechRootedA2RootLine_orbit_card, leechRootedA2RootLineSubgroup_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
