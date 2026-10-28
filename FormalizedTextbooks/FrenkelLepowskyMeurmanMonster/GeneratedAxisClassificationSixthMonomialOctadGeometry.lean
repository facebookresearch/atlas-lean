/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSourceCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSupport0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSupport1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSupport2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSupport3

/-! Original coordinate and sign certificates reconstruct genuine preferred octad-line transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All four genuine source support masks pull back to the original target support. -/
theorem generatedSixth_monomial_octad_support_pullback (k : Fin 4) (f : Fin 231) (i : Fin 24) :
    (generatedSixthMonomialOctadSupportMask (generatedSixthMonomialOctadSourceFamily k f)).testBit
      (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i).val =
    (generatedSixthMonomialOctadSupportMask f).testBit i.val := by
  fin_cases k
  · exact generatedSixth_monomial_octad_support0 f i
  · exact generatedSixth_monomial_octad_support1 f i
  · exact generatedSixth_monomial_octad_support2 f i
  · exact generatedSixth_monomial_octad_support3 f i

/-- On a genuine local octad coordinate, the integer vector is exactly twice its preferred sign. -/
theorem generatedSixth_monomial_octad_integral_coordinate (f : Fin 231) (e : Fin 64)
    (a : Fin 8) :
    generatedSixthMonomialOctadIntegral f e (generatedSixthMonomialOctadCoordinates f a) =
      2 * (if (trialityEvenMask e).testBit a.val then (-1 : ℤ) else 1) := by
  have hs : (generatedSixthMonomialOctadSupportMask f).testBit
      (generatedSixthMonomialOctadCoordinates f a).val = true :=
    (generatedSixth_monomial_octad_support_iff f _).mpr ⟨a, rfl⟩
  have hm : (generatedSixthMonomialOctadNegativeMask f e).testBit
      (generatedSixthMonomialOctadCoordinates f a).val = true ↔
      (trialityEvenMask e).testBit a.val = true := by
    rw [← generatedSixth_monomial_octad_negative_mask,
      ← generatedSixth_monomial_octad_coordinates, griessOctadSignMask_testBit]
    constructor
    · rintro ⟨b, hb, hab⟩
      have hba := golayOctadCoordinate_injective _ hab
      simpa only [hba] using hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  unfold generatedSixthMonomialOctadIntegral
  rw [ite_eq_left hs]
  by_cases ha : (trialityEvenMask e).testBit a.val = true
  · rw [ite_eq_left (hm.mpr ha), ite_eq_left ha]
    decide +kernel
  · rw [ite_eq_right (fun h => ha (hm.mp h)), ite_eq_right ha]
    simp only [mul_one]

/-- Eight true local sign identities imply all 24 original integer-coordinate identities. -/
theorem generatedSixth_monomial_octad_integral_transport (k : Fin 4) (f : Fin 231)
    (e : Fin 64)
    (h : ∀ a : Fin 8,
      (if (trialityEvenMask (generatedSixthMonomialOctadSourceSign k f e)).testBit
        (generatedSixthMonomialOctadSourceCoordinate k f a).val then (-1 : ℤ) else 1) =
      generatedSixthMonomialOctadPhysicalSign k f e *
        (if (trialityEvenMask e).testBit a.val then (-1 : ℤ) else 1))
    (i : Fin 24) :
    generatedSixthMonomialOctadIntegral (generatedSixthMonomialOctadSourceFamily k f)
      (generatedSixthMonomialOctadSourceSign k f e)
      (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i) =
    generatedSixthMonomialOctadPhysicalSign k f e * generatedSixthMonomialOctadIntegral f e i := by
  by_cases hi : (generatedSixthMonomialOctadSupportMask f).testBit i.val = true
  · obtain ⟨a, rfl⟩ := (generatedSixth_monomial_octad_support_iff f i).mp hi
    rw [← generatedSixth_monomial_octad_source_coordinates,
      generatedSixth_monomial_octad_integral_coordinate,
      generatedSixth_monomial_octad_integral_coordinate, h a]
    ring
  · have hs : (generatedSixthMonomialOctadSupportMask
        (generatedSixthMonomialOctadSourceFamily k f)).testBit
        (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i).val ≠ true := by
      rw [generatedSixth_monomial_octad_support_pullback]
      exact hi
    simp only [generatedSixthMonomialOctadIntegral, hi, hs, Bool.false_eq_true, ite_false, mul_zero]

/-- True integer-coordinate transport identifies the original preferred source and target lines. -/
theorem generatedSixth_monomial_octad_permutation_of_integral (k : Fin 4) (f : Fin 231)
    (e : Fin 64)
    (h : ∀ i : Fin 24,
      generatedSixthMonomialOctadIntegral (generatedSixthMonomialOctadSourceFamily k f)
        (generatedSixthMonomialOctadSourceSign k f e)
        (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i) =
      generatedSixthMonomialOctadPhysicalSign k f e * generatedSixthMonomialOctadIntegral f e i) :
    griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2
      (Sum.inr (Sum.inl
        (generatedSixthFinalOctadCacheOctad (generatedSixthMonomialOctadSourceFamily k f),
          generatedSixthMonomialOctadSourceSign k f e))) =
      Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e)) := by
  apply generatedSixth_short_permutation_of_vector
  have hv (i : Fin 24) := congrArg (fun z : ℤ => (z : ℝ)) (h i)
  simp only [Int.cast_mul] at hv
  by_cases hs : (trialityEvenMask e).testBit (generatedSixthMonomialOctadSourceLast k f).val = true
  · right
    funext i
    rw [generatedSixth_monomial_physical_apply]
    simp only [griessShortVector, generatedSixth_monomial_octad_integral, Pi.neg_apply]
    have hh := hv i
    simp only [generatedSixthMonomialOctadPhysicalSign, hs, ite_true, Int.cast_neg,
      Int.cast_one, neg_one_mul] at hh
    rw [hh]
    ring
  · left
    funext i
    rw [generatedSixth_monomial_physical_apply]
    simp only [griessShortVector, generatedSixth_monomial_octad_integral]
    have hh := hv i
    simp only [generatedSixthMonomialOctadPhysicalSign, hs, Bool.false_eq_true, ite_false,
      Int.cast_one, one_mul] at hh
    rw [hh]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
