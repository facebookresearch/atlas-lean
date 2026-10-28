/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddPhaseSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumeratorCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalShortNumerator

/-! Complete actual odd support and preferred-phase certificates fix every nonzero odd
coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual displayed odd coordinate is fixed with the original full preferred-Q sign. -/
theorem generatedSixth_monomial_odd_cached_fixed (k : Fin 4) (f : Fin 512) (j : Fin 24) :
    localShortOperator (generatedSixthCorrectedGenerator (Fin.castAdd 1 k))
      (griessConwayEncode generatedSixthAxis).2.1
      (Sum.inr (Sum.inr (generatedSixthMonomialOddCode f, j))) =
    (griessConwayEncode generatedSixthAxis).2.1
      (Sum.inr (Sum.inr (generatedSixthMonomialOddCode f, j))) := by
  have hr := generatedSixth_monomial_odd_permutation k f j
  have hc : griessShortPermutation (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)).val.2
      (Sum.inr (Sum.inr
        (generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily k f),
          generatedSixthMonomialPairInput k j))) =
      Sum.inr (Sum.inr (generatedSixthMonomialOddCode f, j)) := by
    rw [generatedSixth_corrected_generator_spatial]
    exact hr
  rw [← hc, localShortOperator_image, hc]
  apply generatedSixth_final_short_signed
  rw [generatedSixth_monomial_odd_phase_cache k _ f j hr]
  exact generatedSixth_monomial_odd_numerator_certificate k f j

/-- Every nonzero genuine odd coefficient belongs to the complete checked source support. -/
theorem generatedSixth_monomial_odd_supported_fixed (k : Fin 4) (d : Fin 2048) (j : Fin 24)
    (hn : (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inr (d, j))) ≠ 0) :
    localShortOperator (generatedSixthCorrectedGenerator (Fin.castAdd 1 k))
      (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inr (d, j))) =
    (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inr (d, j))) := by
  have hf : ∃ f : Fin 512, generatedSixthMonomialOddCode f = d :=
    ⟨generatedSixthMonomialOddOwner d, generatedSixth_monomial_odd_support d j hn⟩
  obtain ⟨f, rfl⟩ := hf
  exact generatedSixth_monomial_odd_cached_fixed k f j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
