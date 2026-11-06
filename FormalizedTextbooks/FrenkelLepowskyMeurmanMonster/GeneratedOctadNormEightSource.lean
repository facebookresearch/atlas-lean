/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCountCoefficients

/-! The actual source residues of vectors in a coordinate octad section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual norm-eight vectors inside a specified integral coordinate octad. -/
def GeneratedOctadNormEight (c : Fin 24 → ZMod 2) :=
  {u : leechIntegral // generatedOctadSupported c u.val ∧ leechSquareSum u.val = 64}

/-- The only Golay words supported in the standard octad are zero and that octad. -/
theorem generatedStandardOctad_golay_subcode (c : Fin 24 → ZMod 2)
    (hc : c ∈ golayCode) (hs : ∀ i : Fin 24, 8 ≤ i.val → c i = 0) :
    c = 0 ∨ c = golayStandardOctad := by
  by_cases h0 : c = 0
  · exact Or.inl h0
  by_cases h1 : c = golayStandardOctad
  · exact Or.inr h1
  have ha := golayCode_weight_ge_eight c hc h0
  have hb := golayCode_weight_ge_eight (golayStandardOctad - c)
    (golayCode.sub_mem golayStandardOctad_mem hc) (sub_ne_zero.mpr (Ne.symm h1))
  change 8 ≤ ∑ i, (golayStandardOctad i - c i).val at hb
  have hsum : (∑ i, (c i).val) + (∑ i, (golayStandardOctad i - c i).val) = 8 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i, (golayStandardOctad i).val := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i.val < 8
        · simp only [golayStandardOctad, hi, ↓reduceIte]
          generalize c i = b
          fin_cases b <;> decide +kernel
        · rw [hs i (by omega)]
          simp [golayStandardOctad, hi]
      _ = 8 := golayStandardOctad_weight
  omega

/-- Every actual lattice vector in this section has even source parity and
one of the two genuine supported Golay words. -/
theorem generatedStandardOctad_source (u : leechIntegral)
    (hu : generatedStandardOctadSupported u.val) :
    ∃ c : golayCode, (c.val = 0 ∨ c.val = golayStandardOctad) ∧
      (∀ i, (u.val i : ZMod 4) = 2 * ((c.val i).val : ZMod 4)) ∧
      ((∑ i, u.val i : ℤ) : ZMod 8) = 0 := by
  obtain ⟨m, hm, c, hc, hr, hh⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  have hz : u.val 8 = 0 := hu 8 (by decide)
  rcases hm with rfl | rfl
  · have hr0 : ∀ i, (u.val i : ZMod 4) = 2 * ((c i).val : ZMod 4) := by
      simpa only [Int.cast_zero, zero_add] using hr
    have hcs : ∀ i : Fin 24, 8 ≤ i.val → c i = 0 := by
      intro i hi
      have he := hr0 i
      rw [hu i hi, Int.cast_zero] at he
      have hs : ∀ b : ZMod 2, (0 : ZMod 4) = 2 * (b.val : ZMod 4) → b = 0 := by
        decide +kernel
      exact hs (c i) he
    refine ⟨⟨c, hc⟩, generatedStandardOctad_golay_subcode c hc hcs, hr0, ?_⟩
    simpa only [Int.cast_zero, mul_zero] using hh
  · have he := hr 8
    rw [hz] at he
    have hs : ∀ b : ZMod 2, (0 : ZMod 4) ≠ 1 + 2 * (b.val : ZMod 4) := by
      decide +kernel
    exact False.elim (hs (c 8) (by simpa only [Int.cast_zero, Int.cast_one] using he))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
