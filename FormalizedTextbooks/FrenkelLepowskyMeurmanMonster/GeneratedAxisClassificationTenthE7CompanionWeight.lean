/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSelectedOctadIntersectionData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7CompanionOrbit

/-! Actual whole-octad permutations preserve the complete source intersection weight. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original mask-based intersection count is the weight of the actual encoded word
on all eight standard coordinates. -/
theorem generatedTenth_e7_companion_selected_word (d : Fin 4096) :
    generatedFeasibleContainingCodeSelectedWeight d =
      ∑ i : Fin 24, if i.val < 8 then
        (golayEncoder (golayLabelCoefficients d) i).val else 0 := by
  unfold generatedFeasibleContainingCodeSelectedWeight
  apply Finset.sum_congr rfl
  intro i _
  rw [golayLabelEncoder_match]
  by_cases h8 : i.val < 8 <;> by_cases hb : (golayEncodedMask d.val).testBit i.val = true <;>
    simp [h8, hb]

/-- Every member of the entire actual octad group preserves this complete intersection weight. -/
theorem generatedTenth_e7_companion_selected_invariant
    (g : generatedTenthE7OctadPermutationGroup) (d : Fin 4096) :
    generatedFeasibleContainingCodeSelectedWeight (golayLabelPermutation g.val d) =
      generatedFeasibleContainingCodeSelectedWeight d := by
  rw [generatedTenth_e7_companion_selected_word, generatedTenth_e7_companion_selected_word]
  rw [← Equiv.sum_comp g.val.val (fun i : Fin 24 => if i.val < 8 then
    (golayEncoder (golayLabelCoefficients (golayLabelPermutation g.val d)) i).val else 0)]
  apply Finset.sum_congr rfl
  intro i _
  rw [golayLabelPermutation_coordinate]
  by_cases hi : i.val < 8
  · simp only [ite_eq_left hi,
      ite_eq_left ((generatedTenth_e7_octad_point_membership g i).mpr hi)]
  · simp only [ite_eq_right hi,
      ite_eq_right (fun h => hi ((generatedTenth_e7_octad_point_membership g i).mp h))]

/-- Every actual pointwise permutation fixes each physical standard coordinate. -/
theorem generatedTenth_e7_pointwise_coordinate (p : generatedNinthStandardOctadPointwise)
    (i : Fin 24) (hi : i.val < 8) : p.val.val i = i := by
  have h := p.property ⟨i.val, hi⟩
  have he : Fin.castAdd 16 (⟨i.val, hi⟩ : Fin 8) = i := Fin.ext rfl
  rwa [he] at h

/-- The full actual pointwise action preserves every original mask bit inside the source octad. -/
theorem generatedTenth_e7_pointwise_mask_bit (p : generatedNinthStandardOctadPointwise)
    (d : Fin 4096) (i : Fin 24) (hi : i.val < 8) :
    (golayEncodedMask (golayLabelPermutation p.val d).val).testBit i.val =
      (golayEncodedMask d.val).testBit i.val := by
  have h := congrArg ZMod.val (golayLabelPermutation_coordinate p.val d i)
  rw [generatedTenth_e7_pointwise_coordinate p i hi,
    golayLabelEncoder_match, golayLabelEncoder_match] at h
  by_cases ha : (golayEncodedMask (golayLabelPermutation p.val d).val).testBit i.val = true <;>
    by_cases hb : (golayEncodedMask d.val).testBit i.val = true <;> simp_all

/-- The entire genuine pointwise group preserves the whole standard-octad codeword. -/
theorem generatedTenth_e7_pointwise_octad_mem (p : generatedNinthStandardOctadPointwise) :
    p.val ∈ generatedTenthE7OctadPermutationGroup := by
  apply (generatedTenth_e7_octad_permutation_mem _).mpr
  have hfix : ∀ i : Fin 24, i.val < 5 → p.val.val i = i := by
    intro i hi
    exact generatedTenth_e7_pointwise_coordinate p i (by omega)
  exact golayAutomorphism_preserves_standardOctad p.val hfix

/-- The entire actual pointwise permutation group embeds into the whole octad group. -/
def generatedTenthE7PointwiseOctadElement (p : generatedNinthStandardOctadPointwise) :
    generatedTenthE7OctadPermutationGroup :=
  ⟨p.val, generatedTenth_e7_pointwise_octad_mem p⟩

/-- The original companion is a genuine incident octad of intersection weight two. -/
theorem generatedTenth_e7_companion_incident_actual :
    (2306 : Fin 4096) ∈ generatedFeasibleContainingSelectedIncidentCodes 0 := by
  simp only [generatedFeasibleContainingSelectedIncidentCodes, golayOctads,
    Finset.mem_filter, Finset.mem_univ, true_and]
  decide +kernel

/-- Every pointwise companion orbit member belongs to the entire original sixteen-code sector. -/
theorem generatedTenth_e7_companion_pointwise_orbit_subset :
    MulAction.orbit generatedNinthStandardOctadPointwise (2306 : Fin 4096) ⊆
      (generatedFeasibleContainingSelectedIncidentCodes 0 : Set (Fin 4096)) := by
  rintro d ⟨p, rfl⟩
  change golayLabelPermutation p.val 2306 ∈ generatedFeasibleContainingSelectedIncidentCodes 0
  have ha := generatedTenth_e7_companion_incident_actual
  simp only [generatedFeasibleContainingSelectedIncidentCodes, Finset.mem_filter] at ha ⊢
  refine ⟨(golayLabelPermutation_octad p.val 2306).mpr ha.1, ?_⟩
  have h0 := generatedTenth_e7_pointwise_mask_bit p 2306 0 (by decide)
  have h1 := generatedTenth_e7_pointwise_mask_bit p 2306 1 (by decide)
  rw [show (2306 : Fin 4096).val = 2306 by decide +kernel] at h0 h1
  rw [show (0 : Fin 24).val = 0 by decide +kernel] at h0
  rw [show (1 : Fin 24).val = 1 by decide +kernel] at h1
  rw [show (2306 : Fin 4096).val = 2306 by decide +kernel] at ha
  have hw := generatedTenth_e7_companion_selected_invariant
    (generatedTenthE7PointwiseOctadElement p) 2306
  change generatedFeasibleContainingCodeSelectedWeight (golayLabelPermutation p.val 2306) =
    generatedFeasibleContainingCodeSelectedWeight 2306 at hw
  rw [h0, h1, hw]
  exact ha.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
