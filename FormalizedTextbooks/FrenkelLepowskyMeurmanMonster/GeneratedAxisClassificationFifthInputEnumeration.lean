/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenRootLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddRootLabels
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInputEnumeration

/-! The checked 64 odd and 56 octad image exhaust all 120 original inputs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
-- Enumerate only the 56 pairs supported on the original eight physical coordinates.
/-- Every supported pair input occurs in the actual image certificates. -/
theorem generatedFifth_pair_input_enumeration : ∀ s : Fin 2, ∀ a b : Fin 24,
    a < b → Nat.testBit 0xcccc00 a.val = true → Nat.testBit 0xcccc00 b.val = true →
    (∃ j : Fin 64, generatedFifthOddRootInputData j = Sum.inl (s, a, b)) ∨
      (∃ j : Fin 56, generatedFifthEvenRootInputData j = Sum.inl (s, a, b)) := by
  decide +kernel

/-- Every one of the 64 original octad sign inputs occurs in the actual certificates. -/
theorem generatedFifth_octad_input_enumeration : ∀ e : Fin 64,
    (∃ j : Fin 64, generatedFifthOddRootInputData j = Sum.inr e) ∨
      (∃ j : Fin 56, generatedFifthEvenRootInputData j = Sum.inr e) := by
  decide +kernel

/-- The odd input's finite coordinates equal its genuine preferred integer coordinates. -/
theorem generatedFifth_odd_input_integral (j : Fin 64) :
    griessShortIntegral (generatedFifthOddRootInputLabel j) =
      generatedFourthInputIntegral (generatedFifthOddRootInputData j) := by
  rw [generatedFifthOddRootInputLabel_integral]
  rfl

/-- Every actual supported input is one of the 120 roots whose spatial images are certified. -/
theorem generatedFifth_supported_input_enumeration (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedFourthOctad r) :
    (∃ j : Fin 64, generatedFifthOddRootInputLabel j = r) ∨
      (∃ j : Fin 56, generatedFifthEvenRootInputLabel j = r) := by
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
    rcases generatedFifth_pair_input_enumeration s a b hab hm.1 hm.2 with
      ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      refine ⟨j, generatedFourth_short_label_eq_of_integral ?_⟩
      rw [generatedFifth_odd_input_integral, hj, ← hv]
    · right
      refine ⟨j, generatedFourth_short_label_eq_of_integral ?_⟩
      rw [generatedFifthEvenRootInputLabel_integral, hj, ← hv]
  · have ho : o = generatedFourthOctad := hr
    subst o
    have hv : griessShortIntegral (Sum.inr (Sum.inl (generatedFourthOctad, e))) =
        generatedFourthInputIntegral (Sum.inr e) := by
      simp only [griessShortIntegral, generatedFourthInputIntegral,
        generatedFourthOctad_mask, generatedFourth_root_sign_mask]
    rcases generatedFifth_octad_input_enumeration e with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      refine ⟨j, generatedFourth_short_label_eq_of_integral ?_⟩
      rw [generatedFifth_odd_input_integral, hj, ← hv]
    · right
      refine ⟨j, generatedFourth_short_label_eq_of_integral ?_⟩
      rw [generatedFifthEvenRootInputLabel_integral, hj, ← hv]
  · exact False.elim hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
