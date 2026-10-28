/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortFiniteData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortMatching

/-! Soundness of finite target addresses for the intrinsic actual short action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An admissible target address names a genuine preferred short label. -/
noncomputable def generatedFourthLiftShortTargetLabel (w : ℕ)
    (hw : generatedFourthLiftShortTargetValid w) : GriessShortIndex :=
  if h : generatedFourthLiftShortTargetKind w = true then
    Sum.inr (Sum.inl (generatedFourthEvenRootOctad (generatedFourthLiftShortTargetOctad w),
      generatedFourthLiftShortTargetSign w))
  else Sum.inl (generatedFourthLiftShortTargetPairSign w,
    griessPairIndex (generatedFourthLiftShortTargetFirst w)
      (generatedFourthLiftShortTargetSecond w) (ne_of_lt (hw.resolve_left h)))

/-- An admissible target evaluator is exactly the preferred Q lift of its genuine label. -/
theorem generatedFourth_lift_short_target_q (w : ℕ)
    (hw : generatedFourthLiftShortTargetValid w) :
    generatedFourthLiftShortTargetQ w =
      griessShortQ (generatedFourthLiftShortTargetLabel w hw) := by
  by_cases h : generatedFourthLiftShortTargetKind w = true
  · simp only [generatedFourthLiftShortTargetQ, h, ↓reduceIte,
      generatedFourthLiftShortTargetLabel, ↓reduceDIte]
    exact generatedFourth_lift_short_source_q _ _
  · simp only [generatedFourthLiftShortTargetQ, h, Bool.false_eq_true, ↓reduceIte,
      generatedFourthLiftShortTargetLabel, ↓reduceDIte]
    exact generatedFourth_lift_short_pair_q _ _ _ (hw.resolve_left h)

/-- Every admissible target numerator is its actual original short coordinate times sixteen. -/
theorem generatedFourth_lift_short_target_numerator (w : ℕ)
    (hw : generatedFourthLiftShortTargetValid w) :
    (griessConwayEncode generatedFourthAxis).2.1 (generatedFourthLiftShortTargetLabel w hw) =
      (generatedFourthLiftShortTargetNumerator w : ℝ) / 16 := by
  by_cases h : generatedFourthLiftShortTargetKind w = true
  · simp only [generatedFourthLiftShortTargetLabel, h, ↓reduceDIte,
      generatedFourthLiftShortTargetNumerator, ↓reduceIte]
    exact generatedFourth_lift_short_octad_numerator _ _
  · simp only [generatedFourthLiftShortTargetLabel, h, Bool.false_eq_true, ↓reduceDIte,
      generatedFourthLiftShortTargetNumerator, ↓reduceIte]
    rw [generatedFourth_lift_short_pair_numerator, griessPairIndex_coordinates]
    simp only [hw.resolve_left h, ite_true]

/-- The integer phase sign is exactly the genuine real central character. -/
theorem generatedFourth_lift_short_integer_sign (c : ZMod 2) :
    (((if c = 0 then 1 else -1 : ℤ)) : ℝ) = qSign c := by
  have hc : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc with rfl | rfl <;> simp

/-- A finite full-Q and numerator match certifies a supported actual short coordinate. -/
theorem generatedFourth_lift_short_finite_match_sound
    (r : GriessShortIndex) (q : Q) (n : ℤ) (w : ℕ)
    (hq : q = griessShortQ r)
    (hn : (griessConwayEncode generatedFourthAxis).2.1 r = (n : ℝ) / 16)
    (hm : generatedFourthLiftShortFiniteMatch q n w)
    (hr : (griessConwayEncode generatedFourthAxis).2.1 r ≠ 0) :
    ∃ s c, spinConjugation generatedFourthFlagCorrectedLift.val.1 (griessShortQ r) =
        qCentral c * griessShortQ s ∧
      (griessConwayEncode generatedFourthAxis).2.1 s =
        qSign c * (griessConwayEncode generatedFourthAxis).2.1 r := by
  have hne : n ≠ 0 := by
    intro hz
    apply hr
    rw [hn, hz, Int.cast_zero, zero_div]
  obtain ⟨hw, hb, hc, hnw⟩ := hm hne
  let s := generatedFourthLiftShortTargetLabel w hw
  let c := generatedFourthLiftShortTargetPhase w
  refine ⟨s, c, ?_, ?_⟩
  · rw [← hq, generatedFourth_lift_short_matrix_fast]
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      rw [qCentral_mul_base]
      rw [← generatedFourth_lift_short_target_q w hw]
      exact hb
    · apply toAdd.injective
      rw [qCentral_mul_coeff, griessShortQ_coeff, add_zero]
      exact hc
  · change (griessConwayEncode generatedFourthAxis).2.1
      (generatedFourthLiftShortTargetLabel w hw) = _
    rw [generatedFourth_lift_short_target_numerator, hnw, hn, Int.cast_mul,
      generatedFourth_lift_short_integer_sign]
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
