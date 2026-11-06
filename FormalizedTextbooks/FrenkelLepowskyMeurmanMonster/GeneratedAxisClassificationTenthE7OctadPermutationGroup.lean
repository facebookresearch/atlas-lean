/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayDodecadAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadTransitivity

/-! The entire actual Golay automorphism stabilizer of the source2063 standard octad. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All actual coordinate automorphisms preserving the original standard octad label. -/
def generatedTenthE7OctadPermutationGroup : Subgroup golayAutomorphismSubgroup :=
  MulAction.stabilizer golayAutomorphismSubgroup (2063 : Fin 4096)

private theorem standard_octad_mem : (2063 : Fin 4096) ∈ golayOctads := by
  simp only [golayOctads, Finset.mem_filter, Finset.mem_univ, true_and, golayLabel_weight]
  rw [golayStandardOctad_encoder, golayStandardOctad_weight]

/-- Actual standard-octad membership is precisely preservation of the whole original codeword. -/
theorem generatedTenth_e7_octad_permutation_mem (p : golayAutomorphismSubgroup) :
    p ∈ generatedTenthE7OctadPermutationGroup ↔
      golayPermute p.val golayStandardOctad = golayStandardOctad := by
  change golayLabelPermutation p 2063 = 2063 ↔ _
  constructor
  · intro h
    have hw := golayLabelPermutation_word p 2063
    rw [h, golayStandardOctad_encoder] at hw
    exact hw.symm
  · intro h
    apply golayLabelCoefficients_injective
    apply golayEncoder_injective
    rw [golayLabelPermutation_word, golayStandardOctad_encoder, h]

/-- The actual source standard octad has the entire actual759-octad orbit. -/
theorem generatedTenth_e7_octad_permutation_orbit :
    MulAction.orbit golayAutomorphismSubgroup (2063 : Fin 4096) =
      (golayOctads : Set (Fin 4096)) := by
  apply Set.ext
  intro d
  constructor
  · rintro ⟨p, hp⟩
    rw [← hp]
    change golayLabelPermutation p 2063 ∈ golayOctads
    exact (golayLabelPermutation_octad p 2063).mpr standard_octad_mem
  · intro hd
    have hw : ∑ i : Fin 24, (golayEncoder (golayLabelCoefficients d) i).val = 8 := by
      have h := (Finset.mem_filter.mp hd).2
      rw [golayLabel_weight] at h
      exact h
    have hc : golayEncoder (golayLabelCoefficients d) ∈ golayCode := ⟨_, rfl⟩
    obtain ⟨p, hp⟩ := golayOctad_to_standard _ hc hw
    have he : golayLabelPermutation p d = (2063 : Fin 4096) := by
      apply golayLabelCoefficients_injective
      apply golayEncoder_injective
      rw [golayLabelPermutation_word, hp, golayStandardOctad_encoder]
    refine ⟨p⁻¹, ?_⟩
    change golayLabelActionHom p⁻¹ 2063 = d
    rw [map_inv, ← he]
    exact Equiv.symm_apply_apply _ _

/-- The actual octad orbit has the original verified catalogue cardinality759. -/
theorem generatedTenth_e7_octad_permutation_orbit_card :
    Nat.card (MulAction.orbit golayAutomorphismSubgroup (2063 : Fin 4096)) = 759 := by
  rw [generatedTenth_e7_octad_permutation_orbit]
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, golayOctads_card]

/-- The entire actual standard-octad permutation stabilizer has order322560. -/
theorem generatedTenth_e7_octad_permutation_group_card :
    Nat.card generatedTenthE7OctadPermutationGroup = 322560 := by
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup golayAutomorphismSubgroup (2063 : Fin 4096))
  rw [Nat.card_prod, generatedTenth_e7_octad_permutation_orbit_card,
    golayAutomorphism_card] at h
  change 759 * Nat.card generatedTenthE7OctadPermutationGroup = 244823040 at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
