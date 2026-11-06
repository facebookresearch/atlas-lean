/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightSource

/-! Genuine source congruences of the selected coordinate octad's integral lattice section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The only Golay words supported inside any genuine coordinate octad are zero and that octad. -/
theorem generatedFifthFrame_golay_subcode (c d : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hw : ∑ i, (c i).val = 8) (hd : d ∈ golayCode)
    (hs : ∀ i, c i = 0 → d i = 0) : d = 0 ∨ d = c := by
  by_cases hz : d = 0
  · exact Or.inl hz
  by_cases he : d = c
  · exact Or.inr he
  have ha := golayCode_weight_ge_eight d hd hz
  have hb := golayCode_weight_ge_eight (c - d) (golayCode.sub_mem hc hd)
    (sub_ne_zero.mpr (Ne.symm he))
  change 8 ≤ ∑ i, (c i - d i).val at hb
  have hsum : (∑ i, (d i).val) + (∑ i, (c i - d i).val) = 8 := by
    rw [← Finset.sum_add_distrib, ← hw]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : c i = 0
    · simp [hi, hs i hi]
    · have hbits : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
      have hc1 := (hbits (c i)).resolve_left hi
      rw [hc1]
      generalize d i = b
      fin_cases b <;> decide +kernel
  omega

/-- The original selected code word is zero at a physical coordinate outside the octad. -/
theorem generatedFifthFrame_word_four : golayOctadWord generatedFifthFlagOctad 4 = 0 := by
  simp only [golayOctadWord, generatedFifthFlagOctad_label]
  decide +kernel

/-- Every selected-section vector has even parity and one of two genuine Golay residue words. -/
theorem generatedFifthFrame_source (u : leechIntegral)
    (hu : generatedOctadSupported (golayOctadWord generatedFifthFlagOctad) u.val) :
    ∃ c : golayCode, (c.val = 0 ∨ c.val = golayOctadWord generatedFifthFlagOctad) ∧
      (∀ i, (u.val i : ZMod 4) = 2 * ((c.val i).val : ZMod 4)) ∧
      ((∑ i, u.val i : ℤ) : ZMod 8) = 0 := by
  obtain ⟨m, hm, c, hc, hr, hh⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  have hz : u.val 4 = 0 := hu 4 generatedFifthFrame_word_four
  rcases hm with rfl | rfl
  · have hr0 : ∀ i, (u.val i : ZMod 4) = 2 * ((c i).val : ZMod 4) := by
      simpa only [Int.cast_zero, zero_add] using hr
    have hs : ∀ i, golayOctadWord generatedFifthFlagOctad i = 0 → c i = 0 := by
      intro i hi
      have he := hr0 i
      rw [hu i hi, Int.cast_zero] at he
      have hb : ∀ b : ZMod 2, (0 : ZMod 4) = 2 * (b.val : ZMod 4) → b = 0 := by
        decide +kernel
      exact hb (c i) he
    refine ⟨⟨c, hc⟩, generatedFifthFrame_golay_subcode _ c
      (golayOctadWord_mem_code _) (golayOctadWord_weight _) hc hs, hr0, ?_⟩
    simpa only [Int.cast_zero, mul_zero] using hh
  · have he := hr 4
    rw [hz] at he
    have hs : ∀ b : ZMod 2, (0 : ZMod 4) ≠ 1 + 2 * (b.val : ZMod 4) := by
      decide +kernel
    exact False.elim (hs (c 4) (by simpa only [Int.cast_zero, Int.cast_one] using he))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
