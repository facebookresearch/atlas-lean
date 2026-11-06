/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadData

/-! The finite octad evaluator is bound to genuine catalogue coordinates and integer vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
-- Bind the 231 original code masks to their literal physical supports.
/-- Every literal support mask is the genuine original Golay encoder output. -/
theorem generatedSixth_monomial_octad_support : ∀ f : Fin 231,
    golayEncodedMask (generatedSixthFinalOctadCacheCode f).val =
      generatedSixthMonomialOctadSupportMask f := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Compare all 1848 coordinates with the existing original catalogue certificate data.
/-- Literal eight-coordinate rows equal the original occurring middle-row coordinates. -/
theorem generatedSixth_monomial_octad_middle_coordinates : ∀ f : Fin 231, ∀ a : Fin 8,
    generatedSixthMiddleOctadCoordinates (generatedSixthFinalOctadCacheRepresentative f) a =
      generatedSixthMonomialOctadCoordinates f a := by
  decide +kernel

/-- The finite coordinate rows are the genuine actual catalogue, with no assumed index order. -/
theorem generatedSixth_monomial_octad_coordinates (f : Fin 231) (a : Fin 8) :
    golayOctadCoordinate (generatedSixthFinalOctadCacheOctad f) a =
      generatedSixthMonomialOctadCoordinates f a := by
  rw [generatedSixthFinalOctadCacheOctad,
    generatedSixth_middle_octad_coordinates_certificate,
    generatedSixth_monomial_octad_middle_coordinates]

/-- The finite negative mask is exactly the original preferred sign mask. -/
theorem generatedSixth_monomial_octad_negative_mask (f : Fin 231) (e : Fin 64) :
    griessOctadSignMask (generatedSixthFinalOctadCacheOctad f) e =
      generatedSixthMonomialOctadNegativeMask f e := by
  simp only [griessOctadSignMask, generatedSixthMonomialOctadNegativeMask,
    generatedSixth_monomial_octad_coordinates]

/-- The finite evaluator is the genuine preferred octad integer vector. -/
theorem generatedSixth_monomial_octad_integral (f : Fin 231) (e : Fin 64) (i : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))) i =
      generatedSixthMonomialOctadIntegral f e i := by
  simp only [griessShortIntegral, generatedSixth_final_octad_cache_label,
    generatedSixth_monomial_octad_support, generatedSixth_monomial_octad_negative_mask,
    generatedSixthMonomialOctadIntegral]


/-- The finite negative-position cocode coefficients are the genuine original ones. -/
theorem generatedSixth_monomial_octad_negative_integer (f : Fin 231) (e : Fin 64) (i : Fin 24) :
    griessOctadNegativeInteger (generatedSixthFinalOctadCacheOctad f) e i =
      generatedSixthMonomialOctadNegativeInteger f e i := by
  simp only [griessOctadNegativeInteger, generatedSixth_monomial_octad_negative_mask,
    generatedSixthMonomialOctadNegativeInteger]

/-- Every coordinate row is injective because it is the genuine ordered octad catalogue. -/
theorem generatedSixth_monomial_octad_coordinates_injective (f : Fin 231) :
    Function.Injective (generatedSixthMonomialOctadCoordinates f) := by
  intro a b h
  apply golayOctadCoordinate_injective (generatedSixthFinalOctadCacheOctad f)
  simpa only [generatedSixth_monomial_octad_coordinates] using h

/-- A physical coordinate belongs to the literal support exactly when it is a displayed row. -/
theorem generatedSixth_monomial_octad_support_iff (f : Fin 231) (i : Fin 24) :
    (generatedSixthMonomialOctadSupportMask f).testBit i.val = true ↔
      ∃ a : Fin 8, generatedSixthMonomialOctadCoordinates f a = i := by
  let o := generatedSixthFinalOctadCacheOctad f
  constructor
  · intro hi
    have hm : i ∈ golayMaskSupport (golayEncodedMask (golayOctadLabel o).val) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [o, generatedSixth_final_octad_cache_label,
        generatedSixth_monomial_octad_support] using hi
    let z : golayMaskSupport (golayEncodedMask (golayOctadLabel o).val) := ⟨i, hm⟩
    let e := (golayMaskSupport (golayEncodedMask (golayOctadLabel o).val)).orderIsoOfFin
      (golayOctad_support_card o)
    obtain ⟨a, ha⟩ := e.surjective z
    refine ⟨a, ?_⟩
    rw [← generatedSixth_monomial_octad_coordinates]
    change (e a).val = i
    exact congrArg Subtype.val ha
  · rintro ⟨a, rfl⟩
    have h := golayOctadCoordinate_mem o a
    simpa only [o, generatedSixth_monomial_octad_coordinates,
      generatedSixth_final_octad_cache_label, generatedSixth_monomial_octad_support] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
