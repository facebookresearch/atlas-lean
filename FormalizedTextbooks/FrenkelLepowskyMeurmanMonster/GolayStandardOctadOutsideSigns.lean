/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadSigns

/-! Actual zero-on-octad Golay words allow equal signs at any two outside coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Five original encoder labels whose words vanish on the standard octad. -/
def golayStandardOctadOutsideSeparatorLabel : Fin 5 → Fin 4096 := ![3, 5, 9, 16, 32]

set_option maxHeartbeats 8000000 in
-- Check every standard-octad bit of all five original words.
/-- All five actual source words are zero on the standard octad. -/
theorem golayStandardOctad_outside_separator_zero : ∀ k : Fin 5, ∀ j : Fin 8,
    (golayEncodedMask (golayStandardOctadOutsideSeparatorLabel k).val).testBit j.val = false := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check all pairs of distinct outside coordinates against the five original words.
/-- Every two distinct outside coordinates are separated by an actual zero-on-octad word. -/
theorem golayStandardOctad_outside_separator_bits : ∀ a b : Fin 24,
    8 ≤ a.val → 8 ≤ b.val → a ≠ b → ∃ k : Fin 5,
      (golayEncodedMask (golayStandardOctadOutsideSeparatorLabel k).val).testBit a.val ≠
        (golayEncodedMask (golayStandardOctadOutsideSeparatorLabel k).val).testBit b.val := by
  decide +kernel

/-- Actual Golay words vanishing on the standard octad separate any distinct outside pair. -/
theorem golayStandardOctad_outside_separator (a b : Fin 24)
    (ha : 8 ≤ a.val) (hb : 8 ≤ b.val) (hab : a ≠ b) :
    ∃ c : golayCode, (∀ j : Fin 8, c.val (Fin.castAdd 16 j) = 0) ∧ c.val a ≠ c.val b := by
  obtain ⟨k, hk⟩ := golayStandardOctad_outside_separator_bits a b ha hb hab
  let c := golayCodeLabelEquiv (golayStandardOctadOutsideSeparatorLabel k)
  refine ⟨c, ?_, ?_⟩
  · intro j
    apply (ZMod.val_injective 2)
    change (golayEncoder (golayLabelCoefficients
      (golayStandardOctadOutsideSeparatorLabel k)) (Fin.castAdd 16 j)).val = 0
    rw [golayLabelEncoder_match, Fin.val_castAdd,
      golayStandardOctad_outside_separator_zero k j]
    rfl
  · intro h
    have hv := congrArg (fun z : ZMod 2 => z.val) h
    change (golayEncoder (golayLabelCoefficients
      (golayStandardOctadOutsideSeparatorLabel k)) a).val =
        (golayEncoder (golayLabelCoefficients
          (golayStandardOctadOutsideSeparatorLabel k)) b).val at hv
    rw [golayLabelEncoder_match, golayLabelEncoder_match] at hv
    cases hma : (golayEncodedMask (golayStandardOctadOutsideSeparatorLabel k).val).testBit a.val
      <;> cases hmb :
        (golayEncodedMask (golayStandardOctadOutsideSeparatorLabel k).val).testBit b.val
      <;> simp_all

/-- Every even standard-octad prescription extends to an actual Golay word with equal bits
at any prescribed distinct outside pair. -/
theorem golayStandardOctad_even_signs_equal_outside (bits : Fin 8 → ZMod 2)
    (heven : ∑ j, bits j = 0) (a b : Fin 24)
    (ha : 8 ≤ a.val) (hb : 8 ≤ b.val) (hab : a ≠ b) :
    ∃ c : golayCode, (∀ j : Fin 8, c.val (Fin.castAdd 16 j) = bits j) ∧ c.val a = c.val b := by
  obtain ⟨d, hd⟩ := golayStandardOctad_even_signs bits heven
  by_cases hpair : d.val a = d.val b
  · exact ⟨d, hd, hpair⟩
  · obtain ⟨s, hs, hsep⟩ := golayStandardOctad_outside_separator a b ha hb hab
    refine ⟨d + s, ?_, ?_⟩
    · intro j
      change d.val (Fin.castAdd 16 j) + s.val (Fin.castAdd 16 j) = bits j
      rw [hd j, hs j, add_zero]
    · change d.val a + s.val a = d.val b + s.val b
      have hbit : ∀ w x y z : ZMod 2, w ≠ x → y ≠ z → w + y = x + z := by decide
      exact hbit _ _ _ _ hpair hsep

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
