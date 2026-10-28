/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthEvenRootImages
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddCoverage

/-! The checked 56 odd, 63 octad, and one pair image exhaust all 120 original inputs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
-- Enumerate only the 56 pairs supported on the original eight physical coordinates.
/-- Every supported pair input occurs in the actual image certificates. -/
theorem generatedFourth_pair_input_enumeration : ∀ s : Fin 2, ∀ a b : Fin 24,
    a < b → Nat.testBit 0xcccc00 a.val = true → Nat.testBit 0xcccc00 b.val = true →
    (∃ j : Fin 56, generatedFourthOddRootInputData j = Sum.inl (s, a, b)) ∨
      (∃ j : Fin 63, generatedFourthEvenRootInputData j = Sum.inl (s, a, b)) ∨
        (s = 1 ∧ a = 10 ∧ b = 11) := by
  decide +kernel

/-- Every one of the 64 original octad sign inputs occurs in the actual certificates. -/
theorem generatedFourth_octad_input_enumeration : ∀ e : Fin 64,
    (∃ j : Fin 56, generatedFourthOddRootInputData j = Sum.inr e) ∨
      (∃ j : Fin 63, generatedFourthEvenRootInputData j = Sum.inr e) := by
  decide +kernel

/-- Equality of preferred physical integer vectors identifies their actual short labels. -/
theorem generatedFourth_short_label_eq_of_integral {r s : GriessShortIndex}
    (h : griessShortIntegral r = griessShortIntegral s) : r = s := by
  apply centralizer_shortVector_line_unique r s 1
  change (fun i => (griessShortIntegral r i : ℝ) / Real.sqrt 8) =
    (1 : ℝ) • (fun i => (griessShortIntegral s i : ℝ) / Real.sqrt 8)
  rw [h, one_smul]

/-- The odd input's finite coordinates equal its genuine preferred integer coordinates. -/
theorem generatedFourth_odd_input_integral (j : Fin 56) :
    griessShortIntegral (generatedFourthOddRootInputLabel j) =
      generatedFourthInputIntegral (generatedFourthOddRootInputData j) := by
  rw [generatedFourthOddRootInputLabel_integral]
  rfl

/-- Every actual supported input is one of the 120 roots whose spatial images are certified. -/
theorem generatedFourth_supported_input_enumeration (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedFourthOctad r) :
    (∃ j : Fin 56, generatedFourthOddRootInputLabel j = r) ∨
      (∃ j : Fin 63, generatedFourthEvenRootInputLabel j = r) ∨
        generatedFourthPairOutput = r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · let a := (griessCoordinatePair p).1
    let b := (griessCoordinatePair p).2
    have hab : a < b := by
      have h := (griessCoordinatePairEquiv p).property
      simpa only [griessCoordinatePairs, Finset.mem_filter, Finset.mem_univ, true_and,
        a, b, griessCoordinatePair] using h
    have hm : Nat.testBit 0xcccc00 a.val = true ∧ Nat.testBit 0xcccc00 b.val = true := by
      simpa only [generatedOctadShortSupport, generatedOctadPairSupport,
        generatedFourthOctad_mask] using hr
    have hv : griessShortIntegral (Sum.inl (s, p)) =
        generatedFourthInputIntegral (Sum.inl (s, a, b)) := rfl
    rcases generatedFourth_pair_input_enumeration s a b hab hm.1 hm.2 with
      ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨hs, ha, hb⟩
    · left
      refine ⟨j, generatedFourth_short_label_eq_of_integral ?_⟩
      rw [generatedFourth_odd_input_integral, hj, ← hv]
    · right; left
      refine ⟨j, generatedFourth_short_label_eq_of_integral ?_⟩
      rw [generatedFourthEvenRootInputLabel_integral, hj, ← hv]
    · right; right
      apply generatedFourth_short_label_eq_of_integral
      rw [hv, hs, ha, hb]
      simp only [generatedFourthPairOutput, griessShortIntegral, generatedFourthInputIntegral,
        generatedFourthPairOutput_coordinates]
  · have ho : o = generatedFourthOctad := hr
    subst o
    have hv : griessShortIntegral (Sum.inr (Sum.inl (generatedFourthOctad, e))) =
        generatedFourthInputIntegral (Sum.inr e) := by
      simp only [griessShortIntegral, generatedFourthInputIntegral,
        generatedFourthOctad_mask, generatedFourth_root_sign_mask]
    rcases generatedFourth_octad_input_enumeration e with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      refine ⟨j, generatedFourth_short_label_eq_of_integral ?_⟩
      rw [generatedFourth_odd_input_integral, hj, ← hv]
    · right; left
      refine ⟨j, generatedFourth_short_label_eq_of_integral ?_⟩
      rw [generatedFourthEvenRootInputLabel_integral, hj, ← hv]
  · exact False.elim hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
