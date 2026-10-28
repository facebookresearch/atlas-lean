/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumeratorCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadPhaseSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalShortNumerator

/-! Complete physical and preferred-Q certificates fix every original supported octad coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every occurring genuine octad coordinate is fixed with its entire original preferred phase. -/
theorem generatedSixth_monomial_octad_cached_fixed (k : Fin 4) (f : Fin 231) (e : Fin 64) :
    localShortOperator (generatedSixthCorrectedGenerator (Fin.castAdd 1 k))
      (griessConwayEncode generatedSixthAxis).2.1
      (Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))) =
    (griessConwayEncode generatedSixthAxis).2.1
      (Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))) := by
  have hr := generatedSixth_monomial_octad_source_permutation k f e
  have hc : griessShortPermutation (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)).val.2
      (Sum.inr (Sum.inl
        (generatedSixthFinalOctadCacheOctad (generatedSixthMonomialOctadSourceFamily k f),
          generatedSixthMonomialOctadSourceSign k f e))) =
      Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e)) := by
    rw [generatedSixth_corrected_generator_spatial]
    exact hr
  rw [← hc, localShortOperator_image, hc]
  apply generatedSixth_final_short_signed
  rw [generatedSixth_monomial_octad_phase_cache k _ f e hr]
  change nortonUIntegerSign (generatedSixthMonomialOctadPhase k f e) *
    generatedSixthFinalOctadNumerator
      (golayOctadLabel
        (generatedSixthFinalOctadCacheOctad (generatedSixthMonomialOctadSourceFamily k f)))
      (generatedSixthMonomialOctadSourceSign k f e) =
    generatedSixthFinalOctadNumerator (golayOctadLabel (generatedSixthFinalOctadCacheOctad f)) e
  rw [generatedSixth_final_octad_cache_label, generatedSixth_final_octad_cache_label,
    ← generatedSixth_final_octad_cached_numerator, ← generatedSixth_final_octad_cached_numerator]
  exact generatedSixth_monomial_octad_numerator_certificate k f e

/-- Complete original support coverage extends fixation to every nonzero octad coefficient. -/
theorem generatedSixth_monomial_octad_supported_fixed (k : Fin 4) (o : Fin 759) (e : Fin 64)
    (hn : (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inl (o, e))) ≠ 0) :
    localShortOperator (generatedSixthCorrectedGenerator (Fin.castAdd 1 k))
      (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inl (o, e))) =
    (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inl (o, e))) := by
  have hf : ∃ f : Fin 231, generatedSixthFinalOctadCacheOctad f = o := by
    by_contra h
    exact hn (generatedSixth_final_octad_cached_zero o e h)
  obtain ⟨f, rfl⟩ := hf
  exact generatedSixth_monomial_octad_cached_fixed k f e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
