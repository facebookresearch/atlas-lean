/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSignAxisLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSpatialSignGroup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpatialCount

/-! The genuine projected sign subgroup has 512 elements, all supplied by full-axis lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual quotient image of the admissible 1024 spatial signs. -/
def generatedSeventhProjectedSignSubgroup : Subgroup Co1 :=
  generatedSeventhSpatialSignSubgroup.map (QuotientGroup.mk' signsSubgroup)

private theorem omega_parameter :
    (Pi.single (11 : Fin 12) 1 : SpinIndex) ∈ generatedSeventhSignParameterSpace := by
  change generatedSeventhSignParameterMatrix *ᵥ (Pi.single (11 : Fin 12) 1) = 0
  decide +kernel

private theorem omega_sign_negative :
    generatedSeventhSpatialSignHom (Multiplicative.ofAdd
      (⟨Pi.single (11 : Fin 12) 1, omega_parameter⟩ : generatedSeventhSignParameterSpace)) =
      leechNegativeIdentity := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  change qSign (golayEncoder (Pi.single (11 : Fin 12) 1) i) * x i = -x i
  have h : golayEncoder (Pi.single (11 : Fin 12) 1) i = 1 := by
    simp [golayEncoder, Pi.single_apply, golayGeneratorBit_all_one]
  rw [h, qSign_one, neg_one_mul]

/-- Both genuine central real signs belong to the original admissible sign subgroup. -/
theorem generatedSeventh_signs_le_sign_subgroup :
    signsSubgroup ≤ generatedSeventhSpatialSignSubgroup := by
  intro g hg
  rcases hg with hg | hg
  · have h : g = 1 := Subtype.ext hg
    rw [h]
    exact generatedSeventhSpatialSignSubgroup.one_mem
  · have h : g = leechNegativeIdentity := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      exact hg x
    rw [h, ← omega_sign_negative]
    exact ⟨_, rfl⟩

/-- The quotient image has exactly 512 elements after removing the two actual central signs. -/
theorem generatedSeventhProjectedSignSubgroup_card :
    Nat.card generatedSeventhProjectedSignSubgroup = 512 := by
  have hi : generatedSeventhProjectedSignSubgroup.index =
      generatedSeventhSpatialSignSubgroup.index := by
    change (generatedSeventhSpatialSignSubgroup.map (QuotientGroup.mk' signsSubgroup)).index = _
    rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
    rw [QuotientGroup.ker_mk']
    exact generatedSeventh_signs_le_sign_subgroup
  have h0 := generatedSeventhSpatialSignSubgroup.card_mul_index
  rw [generatedSeventhSpatialSignSubgroup_card, co0_card_exact] at h0
  have h1 := generatedSeventhProjectedSignSubgroup.card_mul_index
  rw [hi, co1_card_exact] at h1
  have hidx : generatedSeventhSpatialSignSubgroup.index = 8120657825280000 :=
    Nat.eq_of_mul_eq_mul_left (by decide : 0 < 1024)
      (h0.trans (by decide : 8315553613086720000 = 1024 * 8120657825280000))
  rw [hidx] at h1
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 8120657825280000)
    (h1.trans (by decide : 4157776806543360000 = 512 * 8120657825280000))

/-- Every genuine projected sign is supplied by a full-coordinate seventh-axis lift. -/
theorem generatedSeventhProjectedSignSubgroup_le_axis :
    generatedSeventhProjectedSignSubgroup ≤ generatedSeventhProjectedAxisStabilizer := by
  rintro g ⟨e, ⟨v, rfl⟩, rfl⟩
  let d := sourceCodeLabelEquiv.symm v.toAdd.val
  have hd : golayLabelCoefficients d = v.toAdd.val := sourceCodeLabelEquiv.apply_symm_apply _
  have hc : generatedSeventhSpatialSignCode v.toAdd = sourceGeneratedSignCode d := by
    apply Subtype.ext
    change golayEncoder v.toAdd.val = golayEncoder (golayLabelCoefficients d)
    rw [hd]
  change QuotientGroup.mk' signsSubgroup
    (golaySignIsometry (generatedSeventhSpatialSignCode v.toAdd)) ∈ _
  rw [hc]
  exact generatedSeventh_sign_mem_projected d (by rw [hd]; exact v.toAdd.property)

/-- The actual projected full-axis stabilizer already has at least 512 distinct sign values. -/
theorem generatedSeventhProjectedAxisStabilizer_sign_card_ge :
    512 ≤ Nat.card generatedSeventhProjectedAxisStabilizer := by
  let : Finite Co1 := co1_finite
  rw [← generatedSeventhProjectedSignSubgroup_card]
  exact Nat.card_le_card_of_injective
    (Subgroup.inclusion generatedSeventhProjectedSignSubgroup_le_axis)
    (Subgroup.inclusion_injective _)

/-- The exact four-element Q kernel supplies at least 2048 full-axis fixing local elements. -/
theorem generatedSeventhLocalAxisStabilizer_sign_card_ge :
    2048 ≤ Nat.card generatedSeventhLocalAxisStabilizer := by
  rw [generatedSeventh_local_stabilizer_card_range]
  exact Nat.mul_le_mul_left 4 generatedSeventhProjectedAxisStabilizer_sign_card_ge

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
