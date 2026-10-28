/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceIndexCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerShortSourceCached

/-! Complete original short source formulas use exact balanced array lookups. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The original slot word at every actual octad and slot address. -/
def generatedNinthOctadSourceSlotIndexCachedWord (o : Fin 759) (j : Fin 8) : ℕ :=
  generatedNinthSourceSlotIndexTree.lookup (o.val * 8 + j.val)

/-- Balanced lookup agrees with the original word, including every zero slot. -/
theorem generatedNinth_octad_source_slot_index_cached_word_actual (o : Fin 759) (j : Fin 8) :
    generatedNinthOctadSourceSlotIndexCachedWord o j = generatedNinthOctadSourceSlotWord o j :=
  generatedNinth_source_slot_index_tree_actual _

/-- The original packed negative-sign word of an octad. -/
def generatedNinthOctadSourceNegativeIndexCachedWord (o : Fin 759) : ℕ :=
  generatedNinthSourceNegativeIndexTree.lookup o.val

/-- Every balanced sign word is exactly the original array sign word. -/
theorem generatedNinth_octad_source_negative_index_cached_word_actual (o : Fin 759) :
    generatedNinthOctadSourceNegativeIndexCachedWord o =
      generatedNinthOctadSlotNegativeWords[o.val]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  exact generatedNinth_source_negative_index_tree_actual _

/-- The complete original signed slot numerator using the exact array representation. -/
def generatedNinthOctadSlotIndexCachedNumerator (o : Fin 759) (j : Fin 8) : ℤ :=
  if generatedNinthOctadSourceSlotIndexCachedWord o j = 0 then 0
  else if (generatedNinthOctadSourceNegativeIndexCachedWord o).testBit j.val then -2 else 2

/-- Every signed numerator retains the original zero condition and negative bit. -/
theorem generatedNinth_octad_slot_index_cached_numerator_actual (o : Fin 759) (j : Fin 8) :
    generatedNinthOctadSlotIndexCachedNumerator o j = generatedNinthOctadSlotNumeratorFast o j := by
  simp only [generatedNinthOctadSlotIndexCachedNumerator, generatedNinthOctadSlotNumeratorFast,
    generatedNinth_octad_source_slot_index_cached_word_actual,
    generatedNinth_octad_source_negative_index_cached_word_actual]

/-- The complete eight-slot Fourier numerator with exact original source labels. -/
def generatedNinthFinalOctadSlotIndexCachedNumerator (o : Fin 759) (e : Fin 64) : ℤ :=
  ∑ j : Fin 8, trialityIntegerMatrix e
    (Fin.ofNat 64 (generatedNinthOctadSourceSlotIndexCachedWord o j % 64)) *
      generatedNinthOctadSlotIndexCachedNumerator o j

/-- All eight original summands agree with the original Fourier numerator. -/
theorem generatedNinth_final_octad_slot_index_cached_numerator_actual
    (o : Fin 759) (e : Fin 64) :
    generatedNinthFinalOctadSlotIndexCachedNumerator o e =
      generatedNinthFinalOctadSlotFastNumerator o e := by
  simp only [generatedNinthFinalOctadSlotIndexCachedNumerator,
    generatedNinthFinalOctadSlotFastNumerator, generatedNinthOctadSourceSlotSign,
    generatedNinth_octad_source_slot_index_cached_word_actual,
    generatedNinth_octad_slot_index_cached_numerator_actual]

/-- The complete preferred-short formula with exact octad source array representation. -/
def generatedNinthLowerShortSourceIndexCachedInteger : GriessShortIndex → ℤ
  | Sum.inl (s, p) => generatedNinthLowerPairSourceInteger s p
  | Sum.inr (Sum.inl (o, e)) => 2 * generatedNinthFinalOctadSlotIndexCachedNumerator o e
  | Sum.inr (Sum.inr (d, i)) =>
      generatedNinthLowerShortSourceCachedInteger (Sum.inr (Sum.inr (d, i)))

/-- Every preferred-short coordinate retains the complete original integer source. -/
theorem generatedNinth_lower_short_source_index_cached_actual (r : GriessShortIndex) :
    generatedNinthLowerShortSourceIndexCachedInteger r =
      generatedNinthLowerShortSourceInteger r := by
  have h : generatedNinthLowerShortSourceIndexCachedInteger r =
      generatedNinthLowerShortSourceCachedInteger r := by
    rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
    · rfl
    · change 2 * generatedNinthFinalOctadSlotIndexCachedNumerator o e =
        2 * generatedNinthFinalOctadSlotFastNumerator o e
      rw [generatedNinth_final_octad_slot_index_cached_numerator_actual]
    · rfl
  exact h.trans (generatedNinth_lower_short_source_cached_actual r)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
