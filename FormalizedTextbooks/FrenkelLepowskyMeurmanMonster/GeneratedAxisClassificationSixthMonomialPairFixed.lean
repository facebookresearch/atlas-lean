/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairNumerator0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairNumerator1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairNumerator2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairNumerator3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalShortNumerator

/-! Every actual pair coordinate is fixed with its complete original preferred-Q phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The checked physical-coordinate numerators equal the genuine source and target numerators. -/
theorem generatedSixth_monomial_pair_integer_fixed (k : Fin 4) (s : Fin 2) (p : Fin 276) :
    nortonUIntegerSign (generatedSixthMonomialPairPhase k (griessCoordinatePair p).1
      (griessCoordinatePair p).2) *
      generatedSixthFinalPairNumerator s (generatedSixthMonomialPairSourceIndex k p) =
        generatedSixthFinalPairNumerator s p := by
  have hp : (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
    (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  have h : nortonUIntegerSign (generatedSixthMonomialPairPhase k (griessCoordinatePair p).1
      (griessCoordinatePair p).2) *
      generatedSixthMonomialPairNumerator s
        (generatedSixthMonomialPairInput k (griessCoordinatePair p).1)
        (generatedSixthMonomialPairInput k (griessCoordinatePair p).2) =
      generatedSixthMonomialPairNumerator s (griessCoordinatePair p).1
        (griessCoordinatePair p).2 := by
    fin_cases k
    · exact generatedSixth_monomial_pair_numerator0 s _ _ hp
    · exact generatedSixth_monomial_pair_numerator1 s _ _ hp
    · exact generatedSixth_monomial_pair_numerator2 s _ _ hp
    · exact generatedSixth_monomial_pair_numerator3 s _ _ hp
  rw [generatedSixth_monomial_pair_source_numerator,
    generatedSixth_monomial_pair_target_numerator] at h
  exact h

/-- Every original preferred pair coordinate is genuinely fixed by each corrected monomial. -/
theorem generatedSixth_monomial_pair_fixed (k : Fin 4) (s : Fin 2) (p : Fin 276) :
    localShortOperator (generatedSixthCorrectedGenerator (Fin.castAdd 1 k))
      (griessConwayEncode generatedSixthAxis).2.1 (Sum.inl (s, p)) =
        (griessConwayEncode generatedSixthAxis).2.1 (Sum.inl (s, p)) := by
  have hr := generatedSixth_monomial_pair_source_permutation k s p
  have hc : griessShortPermutation (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)).val.2
      (Sum.inl (s, generatedSixthMonomialPairSourceIndex k p)) = Sum.inl (s, p) := by
    rw [generatedSixth_corrected_generator_spatial]
    exact hr
  rw [← hc, localShortOperator_image, hc]
  apply generatedSixth_final_short_signed
  rw [generatedSixth_monomial_pair_phase_at_output k _ s p hr]
  change nortonUIntegerSign (generatedSixthMonomialPairPhase k (griessCoordinatePair p).1
      (griessCoordinatePair p).2) *
      generatedSixthFinalPairNumerator s (generatedSixthMonomialPairSourceIndex k p) =
        generatedSixthFinalPairNumerator s p
  exact generatedSixth_monomial_pair_integer_fixed k s p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
