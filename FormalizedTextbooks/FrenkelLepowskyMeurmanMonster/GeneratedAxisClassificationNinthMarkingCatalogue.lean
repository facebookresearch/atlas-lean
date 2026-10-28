/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadMarkingData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalPairMarkings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOddMarkings
public import Mathlib.Data.Finset.Sum

/-! The candidate complete short-coordinate marking catalogue has 144 distinct original
dictionary labels. The actual pair and odd comparisons are unconditional; the complete
short-coordinate comparison below retains the exact missing octad comparison explicitly. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The eight candidate marked addresses in original octad459. -/
def generatedNinthOctadMarkings : Finset (Fin 759 × Fin 64) :=
  generatedNinthOctadMarkedSigns.image (fun e => (459, e))

/-- Candidate octad markings retain exactly their original octad and sign. -/
theorem generatedNinth_mem_octad_markings (o : Fin 759) (e : Fin 64) :
    (o, e) ∈ generatedNinthOctadMarkings ↔
      o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns := by
  simp only [generatedNinthOctadMarkings, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨e', he', ho, rfl⟩
    exact ⟨ho.symm, he'⟩
  · rintro ⟨rfl, he⟩
    exact ⟨e, he, rfl, rfl⟩

/-- The displayed candidate octad addresses are eight distinct dictionary labels. -/
theorem generatedNinth_octad_markings_card : generatedNinthOctadMarkings.card = 8 := by
  rw [generatedNinthOctadMarkings, Finset.card_image_of_injective]
  · exact generatedNinth_octad_marked_signs_card
  · intro a b h
    exact congrArg Prod.snd h

/-- The candidate short-coordinate marking catalogue, retaining all three dictionary families. -/
def generatedNinthShortMarkings : Finset GriessShortIndex :=
  generatedNinthFinalPairMarkings.disjSum
    (generatedNinthOctadMarkings.disjSum generatedNinthOddMarkings)

/-- There are exactly144 distinct candidate short-coordinate markings. -/
theorem generatedNinth_short_markings_card : generatedNinthShortMarkings.card = 144 := by
  simp only [generatedNinthShortMarkings, Finset.card_disjSum,
    generatedNinth_final_pair_markings_card, generatedNinth_octad_markings_card,
    generatedNinth_odd_markings_card]

/-- The actual pair markings are also characterized by absolute coefficient one eighth. -/
theorem generatedNinth_final_pair_marking_abs_iff (s : Fin 2) (p : Fin 276) :
    |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inl (s, p))| = 1 / 8 ↔
      (s, p) ∈ generatedNinthFinalPairMarkings := by
  constructor
  · intro h
    by_contra hn
    have hb := generatedNinth_final_pair_nonmarking_bound s p hn
    rw [h] at hb
    norm_num at hb
  · intro h
    rw [generatedNinth_final_pair_marking_coefficient s p h]
    norm_num

/-- The proved actual pair and odd comparisons extend to the whole short dictionary once
the exact actual octad comparison has been supplied. -/
theorem generatedNinth_short_marking_iff_of_octad_comparison
    (hoctad : ∀ (o : Fin 759) (e : Fin 64),
      |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
        o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns)
    (r : GriessShortIndex) :
    |(griessConwayEncode generatedNinthAxis).2.1 r| = 1 / 8 ↔
      r ∈ generatedNinthShortMarkings := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · simpa only [generatedNinthShortMarkings, Finset.inl_mem_disjSum] using
      generatedNinth_final_pair_marking_abs_iff s p
  · simpa only [generatedNinthShortMarkings, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum,
      generatedNinth_mem_octad_markings] using hoctad o e
  · simpa only [generatedNinthShortMarkings, Finset.inr_mem_disjSum] using
      generatedNinth_final_odd_marking_iff d i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
