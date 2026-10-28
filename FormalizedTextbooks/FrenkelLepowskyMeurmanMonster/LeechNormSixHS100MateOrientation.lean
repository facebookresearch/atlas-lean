/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100PointMover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2PositiveRootStabilizer

/-! A literal root-coordinate swap and central negation reverse the canonical companion orientation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A literal original Mathieu word exchanging the two ordered root coordinates. -/
def leechNormSixHS100MatePermutationWord : List (Fin 4) := [1, 0, 0, 0, 1, 2, 2, 2, 1]

/-- The actual original Golay permutation defined by the literal root-swap word. -/
def leechNormSixHS100MatePermutation : golayAutomorphismSubgroup :=
  golayGeneratingWord leechNormSixHS100MatePermutationWord

/-- The displayed original word exchanges exactly the two physical root positions. -/
theorem leechNormSixHS100Mate_permutation_certificate :
    golayGeneratingWordArray leechNormSixHS100MatePermutationWord 0 = 1 ∧
    golayGeneratingWordArray leechNormSixHS100MatePermutationWord 1 = 0 := by
  decide +kernel

/-- The actual permutation exchanges the original ordered root coordinates. -/
theorem leechNormSixHS100Mate_permutation_spec :
    leechNormSixHS100MatePermutation.val 0 = 1 ∧ leechNormSixHS100MatePermutation.val 1 = 0 := by
  simp only [leechNormSixHS100MatePermutation, leechRootedA2GeneratingWord_apply]
  exact leechNormSixHS100Mate_permutation_certificate

/-- The actual companion of the opposite higher-matrix orientation. -/
def leechNormSixHS100Mate : leechIntegral := leechNormSixHS100Root - leechNormSixHS100Companion

/-- The literal root swap reverses the complete original difference root. -/
theorem leechNormSixHS100Mate_permutation_root :
    leechIntegralAction (golayPermutationIsometry leechNormSixHS100MatePermutation)
      leechNormSixHS100Root = -leechNormSixHS100Root := by
  apply Subtype.ext
  rw [leechNormSixHS100Permutation_action]
  funext i
  obtain ⟨h0, h1⟩ := leechNormSixHS100Mate_permutation_spec
  have hp0 : leechNormSixHS100MatePermutation.val.symm i = 0 ↔ i = 1 := by
    rw [Equiv.symm_apply_eq, h0]
  have hp1 : leechNormSixHS100MatePermutation.val.symm i = 1 ↔ i = 0 := by
    rw [Equiv.symm_apply_eq, h1]
  simp only [golayIntegerPermute, leechNormSixHS100Root, leechNormSixHS100RootIntegral,
    Submodule.coe_neg, Pi.neg_apply, hp0, hp1]
  by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> simp_all

/-- The literal root swap sends the entire companion to its difference from the root. -/
theorem leechNormSixHS100Mate_permutation_companion :
    leechIntegralAction (golayPermutationIsometry leechNormSixHS100MatePermutation)
      leechNormSixHS100Companion = leechNormSixHS100Companion - leechNormSixHS100Root := by
  apply Subtype.ext
  rw [leechNormSixHS100Permutation_action]
  funext i
  have hp0 : leechNormSixHS100MatePermutation.val.symm i = 0 ↔ i = 1 := by
    rw [Equiv.symm_apply_eq, leechNormSixHS100Mate_permutation_spec.1]
  simp only [golayIntegerPermute, leechNormSixHS100Companion,
    leechNormSixHS100CompanionIntegral, leechNormSixHS100Root, leechNormSixHS100RootIntegral,
    Submodule.coe_sub, Pi.sub_apply, hp0]
  by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> simp_all

/-- The literal original root swap followed by genuine central Golay negation. -/
def leechNormSixHS100MateOrientation : leechIsomSubgroup :=
  golaySignIsometry leechRootNegationCode * golayPermutationIsometry leechNormSixHS100MatePermutation

/-- The complete original positive difference root is fixed by the mate-orientation word. -/
theorem leechNormSixHS100MateOrientation_root :
    leechIntegralAction leechNormSixHS100MateOrientation leechNormSixHS100Root = leechNormSixHS100Root := by
  rw [leechNormSixHS100MateOrientation, map_mul, LinearEquiv.mul_apply,
    leechRootNegationCode_action, leechNormSixHS100Mate_permutation_root, neg_neg]

/-- The entire original companion is sent to the other genuine higher-matrix orientation. -/
theorem leechNormSixHS100MateOrientation_companion :
    leechIntegralAction leechNormSixHS100MateOrientation leechNormSixHS100Companion = leechNormSixHS100Mate := by
  rw [leechNormSixHS100MateOrientation, map_mul, LinearEquiv.mul_apply,
    leechRootNegationCode_action, leechNormSixHS100Mate_permutation_companion, neg_sub]
  rfl

/-- The literal mate-orientation word sends the other companion back to the original one. -/
theorem leechNormSixHS100MateOrientation_mate :
    leechIntegralAction leechNormSixHS100MateOrientation leechNormSixHS100Mate = leechNormSixHS100Companion := by
  rw [leechNormSixHS100Mate, map_sub, leechNormSixHS100MateOrientation_root,
    leechNormSixHS100MateOrientation_companion, leechNormSixHS100Mate, sub_sub_cancel]

/-- The two complete original higher-matrix companion orientations are distinct. -/
theorem leechNormSixHS100Mate_ne : leechNormSixHS100Companion ≠ leechNormSixHS100Mate := by
  intro h
  have he := congrArg (fun u : leechIntegral => u.val 0) h
  norm_num [leechNormSixHS100Mate, leechNormSixHS100Root, leechNormSixHS100RootIntegral,
    leechNormSixHS100Companion, leechNormSixHS100CompanionIntegral] at he

/-- The actual positive-root Conway group preserving both complete companion orientations. -/
def leechNormSixHS100MateGroup : Subgroup leechIsomSubgroup where
  carrier := {g | leechIntegralAction g leechNormSixHS100Root = leechNormSixHS100Root ∧
    (leechIntegralAction g leechNormSixHS100Companion = leechNormSixHS100Companion ∨
     leechIntegralAction g leechNormSixHS100Companion = leechNormSixHS100Mate)}
  one_mem' := by
    constructor
    · rw [map_one]
      rfl
    · left
      rw [map_one]
      rfl
  mul_mem' := by
    rintro a b ⟨hax, hay⟩ ⟨hbx, hby⟩
    constructor
    · rw [map_mul, LinearEquiv.mul_apply, hbx, hax]
    · rw [map_mul, LinearEquiv.mul_apply]
      rcases hby with hby | hby
      · rw [hby]
        exact hay
      · rw [hby, leechNormSixHS100Mate, map_sub, hax]
        rcases hay with hay | hay
        · right
          rw [hay]
        · left
          rw [hay, leechNormSixHS100Mate, sub_sub_cancel]
  inv_mem' := by
    rintro a ⟨hax, hay⟩
    have hx : leechIntegralAction a⁻¹ leechNormSixHS100Root = leechNormSixHS100Root := by
      apply (leechIntegralAction a).injective
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, hax]
      rfl
    refine ⟨hx, ?_⟩
    rcases hay with hay | hay
    · left
      apply (leechIntegralAction a).injective
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, hay]
      rfl
    · right
      apply (leechIntegralAction a).injective
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        leechNormSixHS100Mate, map_sub, hax, hay, leechNormSixHS100Mate, sub_sub_cancel]
      rfl

/-- The literal companion-orientation swap belongs to the actual two-companion group. -/
theorem leechNormSixHS100MateOrientation_mem : leechNormSixHS100MateOrientation ∈ leechNormSixHS100MateGroup :=
  ⟨leechNormSixHS100MateOrientation_root, Or.inr leechNormSixHS100MateOrientation_companion⟩

/-- The complete actual flag stabilizer embeds in the original two-companion group. -/
theorem leechNormSixHS100MateGroup_contains_flag :
    leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion ≤
      leechNormSixHS100MateGroup := by
  intro g hg
  obtain ⟨hx, hy⟩ := (leechNormSixActualPairStabilizer_mem _ _ g).mp hg
  exact ⟨hx, Or.inl hy⟩

/-- The actual companion stabilizer in the two-companion group is the original simultaneous flag group. -/
def leechNormSixHS100MateFlagEquiv :
    MulAction.stabilizer leechNormSixHS100MateGroup leechNormSixHS100Companion ≃*
      leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion where
  toFun g := ⟨g.val.val, (leechNormSixActualPairStabilizer_mem _ _ _).mpr
    ⟨g.val.property.1, g.property⟩⟩
  invFun g := ⟨⟨g.val, leechNormSixHS100MateGroup_contains_flag g.property⟩,
    ((leechNormSixActualPairStabilizer_mem _ _ _).mp g.property).2⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    rfl

/-- The original companion orbit consists of exactly the two complete physical orientations. -/
theorem leechNormSixHS100MateGroup_orbit :
    MulAction.orbit leechNormSixHS100MateGroup leechNormSixHS100Companion =
      {leechNormSixHS100Companion, leechNormSixHS100Mate} := by
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    exact g.property.2
  · rintro (rfl | rfl)
    · exact MulAction.mem_orbit_self _
    · exact ⟨⟨leechNormSixHS100MateOrientation, leechNormSixHS100MateOrientation_mem⟩,
        leechNormSixHS100MateOrientation_companion⟩

/-- The actual original two-companion orbit has cardinality two. -/
theorem leechNormSixHS100MateGroup_orbit_card :
    Nat.card (MulAction.orbit leechNormSixHS100MateGroup leechNormSixHS100Companion) = 2 := by
  rw [leechNormSixHS100MateGroup_orbit]
  change ({leechNormSixHS100Companion, leechNormSixHS100Mate} : Set leechIntegral).ncard = 2
  exact Set.ncard_pair leechNormSixHS100Mate_ne

/-- The actual canonical positive-root two-companion group has88704000 original Conway elements. -/
theorem leechNormSixHS100MateGroup_card : Nat.card leechNormSixHS100MateGroup = 88704000 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    leechNormSixHS100MateGroup leechNormSixHS100Companion)
  rw [Nat.card_prod, leechNormSixHS100MateGroup_orbit_card,
    Nat.card_congr leechNormSixHS100MateFlagEquiv.toEquiv,
    leechNormSixActualPairStabilizer_card _ _ leechNormSixHS100Root_square
      leechNormSixHS100Companion_square leechNormSixHS100Flag_pairing] at h
  exact h.symm

/-- The complete flag group and the literal mate word generate the entire actual two-companion group. -/
theorem leechNormSixHS100MateGroup_generates :
    leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion ⊔
      Subgroup.zpowers leechNormSixHS100MateOrientation = leechNormSixHS100MateGroup := by
  apply le_antisymm
  · apply sup_le leechNormSixHS100MateGroup_contains_flag
    exact Subgroup.zpowers_le.mpr leechNormSixHS100MateOrientation_mem
  · intro g hg
    let S := leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion ⊔
      Subgroup.zpowers leechNormSixHS100MateOrientation
    rcases hg.2 with hy | hy
    · exact Subgroup.mem_sup_left ((leechNormSixActualPairStabilizer_mem _ _ g).mpr ⟨hg.1, hy⟩)
    · have hm : leechNormSixHS100MateOrientation ∈ S :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers leechNormSixHS100MateOrientation)
      have hh : leechNormSixHS100MateOrientation * g ∈
          leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion := by
        apply (leechNormSixActualPairStabilizer_mem _ _ _).mpr
        constructor
        · rw [map_mul, LinearEquiv.mul_apply, hg.1, leechNormSixHS100MateOrientation_root]
        · rw [map_mul, LinearEquiv.mul_apply, hy, leechNormSixHS100MateOrientation_mate]
      have h := S.mul_mem (S.inv_mem hm) (Subgroup.mem_sup_left hh)
      simpa only [inv_mul_cancel_left] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
