/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionRoots

/-! Integer reconstruction in the actual selected section and its eight-root basis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every displayed local position is genuinely in the selected coordinate octad. -/
theorem generatedFifthFrame_word_positions : ∀ j : Fin 8,
    golayOctadWord generatedFifthFlagOctad (generatedFifthFramePositions j) = 1 := by
  simp only [golayOctadWord, generatedFifthFlagOctad_label]
  decide +kernel

/-- The actual selected word is zero precisely outside its eight displayed positions. -/
theorem generatedFifthFrame_word_zero : ∀ i : Fin 24,
    golayOctadWord generatedFifthFlagOctad i = 0 ↔
      ¬ (i.val < 4 ∨ (16 ≤ i.val ∧ i.val < 20)) := by
  simp only [golayOctadWord, generatedFifthFlagOctad_label]
  decide +kernel

/-- Extraction of the eight actual local coordinates from a selected-section vector. -/
def generatedFifthFrameLocalCoordinates (u : leechIntegral) : Fin 8 → ℤ :=
  fun j => u.val (generatedFifthFramePositions j)

/-- Extraction followed by insertion recovers every vector in the actual selected section. -/
theorem generatedFifthFrame_insert_local (u : leechIntegral)
    (hu : generatedOctadSupported (golayOctadWord generatedFifthFlagOctad) u.val) :
    generatedFifthFrameInsert (generatedFifthFrameLocalCoordinates u) = u.val := by
  have hout (i : Fin 24) (hi : ¬ (i.val < 4 ∨ (16 ≤ i.val ∧ i.val < 20))) :
      u.val i = 0 := hu i ((generatedFifthFrame_word_zero i).mpr hi)
  ext i
  fin_cases i <;>
    simp [generatedFifthFrameInsert, generatedFifthFrameLocalCoordinates,
      generatedFifthFramePositions, hout]

/-- Insertion preserves the actual sum of integral coordinates. -/
theorem generatedFifthFrame_insert_sum (v : Fin 8 → ℤ) :
    ∑ i, generatedFifthFrameInsert v i = ∑ j, v j := by
  simp [generatedFifthFrameInsert, Fin.sum_univ_succ]

/-- Selected-section local coordinates satisfy the exact integer root-basis divisibilities. -/
theorem generatedFifthFrame_local_divisibility (u : leechIntegral)
    (hu : generatedOctadSupported (golayOctadWord generatedFifthFlagOctad) u.val) :
    let v := generatedFifthFrameLocalCoordinates u
    2 ∣ v 7 ∧ (∀ i, 4 ∣ v 7 - v i) ∧ 8 ∣ ∑ i, v i := by
  obtain ⟨c, hc, hr, hh⟩ := generatedFifthFrame_source u hu
  let v := generatedFifthFrameLocalCoordinates u
  have hres : ∃ b : ZMod 2, ∀ j, (v j : ZMod 4) = 2 * (b.val : ZMod 4) := by
    rcases hc with hc | hc
    · refine ⟨0, ?_⟩
      intro j
      simpa only [v, generatedFifthFrameLocalCoordinates, hc, Pi.zero_apply] using
        hr (generatedFifthFramePositions j)
    · refine ⟨1, ?_⟩
      intro j
      simpa only [v, generatedFifthFrameLocalCoordinates, hc,
        generatedFifthFrame_word_positions] using hr (generatedFifthFramePositions j)
  obtain ⟨b, hb⟩ := hres
  have hfour : 4 ∣ v 7 - 2 * (b.val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
    push_cast
    rw [hb 7, sub_self]
  have htwo : 2 ∣ v 7 := by
    have he := dvd_add (dvd_trans (by decide : (2 : ℤ) ∣ 4) hfour)
      (dvd_mul_right (2 : ℤ) (b.val : ℤ))
    simpa only [sub_add_cancel] using he
  refine ⟨htwo, ?_, ?_⟩
  · intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
    rw [Int.cast_sub, hb 7, hb i, sub_self]
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
    rw [← generatedFifthFrame_insert_local u hu,
      generatedFifthFrame_insert_sum] at hh
    exact hh

/-- Every genuine selected-section local vector is an integer combination of the eight roots. -/
theorem generatedFifthFrame_local_reconstruction (u : leechIntegral)
    (hu : generatedOctadSupported (golayOctadWord generatedFifthFlagOctad) u.val) :
    generatedOctadIntegerRootMatrix *ᵥ
      generatedOctadIntegerRootCoordinates (generatedFifthFrameLocalCoordinates u) =
        generatedFifthFrameLocalCoordinates u := by
  obtain ⟨h2, h4, h8⟩ := generatedFifthFrame_local_divisibility u hu
  exact generatedFifthFrame_root_coordinates _ h2 h4 h8

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
