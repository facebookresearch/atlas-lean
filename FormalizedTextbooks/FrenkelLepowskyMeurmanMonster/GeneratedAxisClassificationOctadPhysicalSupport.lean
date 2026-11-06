/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadAxisData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection

/-! The actual 120 supported labels are precisely the physical short lines
contained in the coordinate octad section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual octad short-label support is exactly physical coordinate support. -/
theorem generatedOctadShortSupport_iff_physical (o : Fin 759) (r : GriessShortIndex) :
    generatedOctadShortSupport o r ↔
      ∀ i : Fin 24, (golayEncodedMask (golayOctadLabel o).val).testBit i.val = false →
        griessShortVector r i = 0 := by
  constructor
  · exact generatedAxisE8_short_support_zero o r
  · intro h
    have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
    rcases r with ⟨s, p⟩ | (⟨q, e⟩ | ⟨d, j⟩)
    · change generatedOctadPairSupport o p
      have ha : griessShortVector (Sum.inl (s, p)) (griessCoordinatePair p).1 ≠ 0 := by
        simp [griessShortVector, griessShortIntegral, griessCoordinatePair_ne p, hsqrt]
      have hb : griessShortVector (Sum.inl (s, p)) (griessCoordinatePair p).2 ≠ 0 := by
        simp only [griessShortVector, griessShortIntegral, (griessCoordinatePair_ne p).symm,
          ite_false, ite_true, mul_zero, mul_one, zero_add, div_ne_zero_iff]
        split_ifs <;> norm_num [hsqrt]
      constructor
      · cases hm : (golayEncodedMask (golayOctadLabel o).val).testBit
          (griessCoordinatePair p).1.val
        · exact False.elim (ha (h _ hm))
        · rfl
      · cases hm : (golayEncodedMask (golayOctadLabel o).val).testBit
          (griessCoordinatePair p).2.val
        · exact False.elim (hb (h _ hm))
        · rfl
    · change q = o
      have hsub : golayOctadSupport q ⊆ golayOctadSupport o := by
        intro i hi
        have hq : (golayEncodedMask (golayOctadLabel q).val).testBit i.val = true :=
          (Finset.mem_filter.mp hi).2
        have hn := (generatedAxis_octad_coordinate_ne_zero q e i).mpr hq
        change i ∈ golayMaskSupport (golayEncodedMask (golayOctadLabel o).val)
        simp only [golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hm : (golayEncodedMask (golayOctadLabel o).val).testBit i.val
        · exact False.elim (hn (h i hm))
        · rfl
      have he : golayOctadSupport q = golayOctadSupport o :=
        Finset.eq_of_subset_of_card_le hsub (by simp)
      apply golayOctadWord_injective
      ext i
      have hc : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b := by decide +kernel
      apply hc
      rw [golayOctadWord_ne_zero_iff, golayOctadWord_ne_zero_iff, he]
    · have hex : ∃ i : Fin 24, i ∉ golayOctadSupport o := by
        by_contra hn
        have hall : golayOctadSupport o = Finset.univ := by
          ext i
          simp only [Finset.mem_univ, iff_true]
          exact Classical.not_not.mp (not_exists.mp hn i)
        have hc := golayOctadSupport_card o
        rw [hall] at hc
        norm_num at hc
      obtain ⟨i, hi⟩ := hex
      have ho : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = false := by
        simpa only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
          Finset.mem_univ, true_and, Bool.not_eq_true] using hi
      have hz := h i ho
      have hn : griessShortVector (Sum.inr (Sum.inr (d, j))) i ≠ 0 := by
        simp only [griessShortVector, griessShortIntegral, div_ne_zero_iff]
        split_ifs <;> norm_num [hsqrt]
      exact False.elim (hn hz)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
