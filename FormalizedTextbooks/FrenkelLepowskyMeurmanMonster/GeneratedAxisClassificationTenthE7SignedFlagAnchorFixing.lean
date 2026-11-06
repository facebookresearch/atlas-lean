/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignedFlagCandidates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7StandardNormalPair
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7BinaryIntegerSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitGroup

/-! Every complete actual signed candidate preserves the original anchored short-root line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The actual anchored root has its complete original two-coordinate source. -/
theorem generatedTenth_e7_signed_anchor_root_coordinates : ∀ i : Fin 24,
    (generatedTenthE7OrbitNodeRoot 0).val i =
      if i = 4 then 4 else if i = 5 then -4 else 0 := by
  rw [generatedTenth_e7_orbit_node_physical]
  decide +kernel

/-- The full genuine signed coordinate action on the actual anchor root. -/
theorem generatedTenth_e7_signed_flag_anchor_coordinate
    (v : generatedTenthE7SignedFlagCandidates) (i : Fin 24) :
    (leechIntegralAction (generatedTenthE7SignedFlagSpatial v)
      (generatedTenthE7OrbitNodeRoot 0)).val i =
      if v.2.val.val i = 0 then (generatedTenthE7OrbitNodeRoot 0).val (v.1.val.val.val.symm i)
        else -(generatedTenthE7OrbitNodeRoot 0).val (v.1.val.val.val.symm i) := by
  unfold generatedTenthE7SignedFlagSpatial golayMonomialPair
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation]
  rfl

/-- Every entire signed candidate acts on the original anchor root by one actual integer sign. -/
theorem generatedTenth_e7_signed_flag_anchor_orientation
    (v : generatedTenthE7SignedFlagCandidates) :
    leechIntegralAction (generatedTenthE7SignedFlagSpatial v) (generatedTenthE7OrbitNodeRoot 0) =
        generatedTenthE7IntegerSign (v.2.val.val 4) • generatedTenthE7OrbitNodeRoot 0 ∨
      leechIntegralAction (generatedTenthE7SignedFlagSpatial v) (generatedTenthE7OrbitNodeRoot 0) =
        -generatedTenthE7IntegerSign (v.2.val.val 4) • generatedTenthE7OrbitNodeRoot 0 := by
  have hc : v.2.val.val 4 = v.2.val.val 5 := v.2.property.1
  rcases generatedTenth_e7_standard_flag_normal_pair v.1 with ⟨h4, h5⟩ | ⟨h4, h5⟩
  · left
    apply Subtype.ext
    funext i
    rw [generatedTenth_e7_signed_flag_anchor_coordinate]
    change _ = generatedTenthE7IntegerSign (v.2.val.val 4) *
      (generatedTenthE7OrbitNodeRoot 0).val i
    simp_rw [generatedTenth_e7_signed_anchor_root_coordinates]
    have hp4 : v.1.val.val.val.symm i = 4 ↔ i = 4 := by rw [Equiv.symm_apply_eq, h4]
    have hp5 : v.1.val.val.val.symm i = 5 ↔ i = 5 := by rw [Equiv.symm_apply_eq, h5]
    simp only [hp4, hp5]
    by_cases hi4 : i = 4
    · subst i
      simp [generatedTenthE7IntegerSign]
    · by_cases hi5 : i = 5
      · subst i
        simp [generatedTenthE7IntegerSign, hc]
        split_ifs <;> norm_num
      · simp [hi4, hi5]
  · right
    apply Subtype.ext
    funext i
    rw [generatedTenth_e7_signed_flag_anchor_coordinate]
    change _ = -generatedTenthE7IntegerSign (v.2.val.val 4) *
      (generatedTenthE7OrbitNodeRoot 0).val i
    simp_rw [generatedTenth_e7_signed_anchor_root_coordinates]
    have hp4 : v.1.val.val.val.symm i = 4 ↔ i = 5 := by rw [Equiv.symm_apply_eq, h4]
    have hp5 : v.1.val.val.val.symm i = 5 ↔ i = 4 := by rw [Equiv.symm_apply_eq, h5]
    simp only [hp4, hp5]
    by_cases hi4 : i = 4
    · subst i
      simp [generatedTenthE7IntegerSign]
      split_ifs <;> norm_num
    · by_cases hi5 : i = 5
      · subst i
        simp [generatedTenthE7IntegerSign, hc]
      · simp [hi4, hi5]

/-- Every actual signed candidate fixes the complete original anchored short class. -/
theorem generatedTenth_e7_signed_flag_anchor_class (v : generatedTenthE7SignedFlagCandidates) :
    leechModTwoAction (generatedTenthE7SignedFlagSpatial v) (generatedTenthE7OrbitNodeClass 0) =
      generatedTenthE7OrbitNodeClass 0 := by
  change leechReduction (leechIntegralAction (generatedTenthE7SignedFlagSpatial v)
    (generatedTenthE7OrbitNodeRoot 0)) = leechReduction (generatedTenthE7OrbitNodeRoot 0)
  rcases generatedTenth_e7_signed_flag_anchor_orientation v with h | h
  all_goals
    rw [h]
    by_cases hz : v.2.val.val 4 = 0 <;>
      simp [generatedTenthE7IntegerSign, hz, leechReduction_neg]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
