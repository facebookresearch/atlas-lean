/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingNormalizedShortOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OctadPairAction

/-! The actual companion octad has a sixteen-element pointwise permutation orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complete genuine pointwise-octad permutation group acts on original Golay labels. -/
instance generatedTenthE7PointwiseCompanionAction :
    MulAction generatedNinthStandardOctadPointwise (Fin 4096) :=
  MulAction.compHom (Fin 4096)
    (golayLabelActionHom.comp generatedNinthStandardOctadPointwise.subtype)

/-- Fixing the actual companion label forces an actual pointwise permutation to be identity. -/
theorem generatedTenth_e7_companion_pointwise_kernel
    (g : generatedNinthStandardOctadPointwise) (hg : g • (2306 : Fin 4096) = 2306) :
    g = 1 := by
  obtain ⟨j, hj⟩ := generatedTenth_e8_standard_affine_surjective g
  have hjv : g.val = generatedNinthStandardOctadRepresentative j :=
    (congrArg Subtype.val hj).symm
  have hp : golayLabelPermutation g.val 2306 = 2306 := hg
  have hs : ∀ i : Fin 24, (golayEncodedMask 2306).testBit i.val = true →
      (golayEncodedMask 2306).testBit
        ((generatedNinthStandardOctadRepresentative j).val i).val = true := by
    intro i hi
    rw [← hjv]
    have hc := golayLabelPermutation_coordinate g.val 2306 i
    rw [hp] at hc
    have hv := congrArg ZMod.val hc
    rw [golayLabelEncoder_match, golayLabelEncoder_match] at hv
    rw [show (2306 : Fin 4096).val = 2306 by decide +kernel] at hv
    rw [ite_eq_left hi] at hv
    by_contra hn
    rw [ite_eq_right hn] at hv
    omega
  have hj0 := generatedFeasibleContaining_normalized_permutation_support j hs
  apply Subtype.ext
  rw [hjv, hj0, generatedFeasibleContaining_normalized_permutation_zero]
  rfl

/-- The entire actual companion-label stabilizer inside the pointwise group is trivial. -/
theorem generatedTenth_e7_companion_pointwise_stabilizer :
    MulAction.stabilizer generatedNinthStandardOctadPointwise (2306 : Fin 4096) = ⊥ := by
  apply le_antisymm
  · intro g hg
    change g = 1
    exact generatedTenth_e7_companion_pointwise_kernel g hg
  · exact bot_le

/-- The whole genuine pointwise permutation group has an actual sixteen-companion orbit. -/
theorem generatedTenth_e7_companion_pointwise_orbit_card :
    Nat.card (MulAction.orbit generatedNinthStandardOctadPointwise (2306 : Fin 4096)) = 16 := by
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup generatedNinthStandardOctadPointwise
      (2306 : Fin 4096))
  rw [Nat.card_prod, generatedTenth_e7_companion_pointwise_stabilizer,
    Subgroup.card_bot, mul_one, generatedNinth_standard_octad_pointwise_card] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
