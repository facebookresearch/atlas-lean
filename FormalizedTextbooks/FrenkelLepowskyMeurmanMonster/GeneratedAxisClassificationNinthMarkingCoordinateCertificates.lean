/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingClasses

/-! Exact integer and binary coordinates identify each intrinsic preferred marking lift.
This helper retains both finite coordinate certificates explicitly. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix

/-- The two exact coordinate obligations for an original candidate marking label. -/
structure GeneratedNinthMarkingCoordinateCertificate (k : Fin 144) : Prop where
  /-- The displayed integer coordinates multiply to the genuine integral short vector. -/
  integer : generatedNinthShortRowTargetIntegral (generatedNinthMarkingLabel k) =
    leechBasisMatrix *ᵥ generatedNinthMarkingCoordinates k
  /-- The displayed packed vector is the actual binary coordinate vector. -/
  binary : leechHyperbolicInverse *ᵥ integerParity (generatedNinthMarkingCoordinates k) =
    monsterCo1GeometryBinaryMaskDecode (generatedNinthMarkingMask k)

/-- Both coordinate certificates identify the actual intrinsic preferred short lift's base. -/
theorem generatedNinth_marking_coordinate_actual (k : Fin 144)
    (h : GeneratedNinthMarkingCoordinateCertificate k) :
    toAdd (griessShortQ (generatedNinthMarkingLabel k)).base =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthMarkingMask k) := by
  rw [← monsterNortonShortQ_eq]
  apply generatedNinth_preferred_short_mask_of_coordinates
    (generatedNinthMarkingLabel k) (generatedNinthMarkingCoordinates k)
  · rw [← generatedNinth_short_row_target_integral_actual]
    exact h.integer
  · exact h.binary

/-- Both coordinate certificates identify the actual lattice class in the hyperbolic basis. -/
theorem generatedNinth_marking_class_binary_of_certificate (k : Fin 144)
    (h : GeneratedNinthMarkingCoordinateCertificate k) :
    leechHyperbolicCoordinates (generatedNinthMarkingClass k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthMarkingMask k) := by
  exact generatedNinth_marking_coordinate_actual k h

/-- A checked coordinate row identifies its full actual lattice quotient class. -/
theorem generatedNinth_marking_class_of_certificate (k : Fin 144)
    (h : GeneratedNinthMarkingCoordinateCertificate k) :
    generatedNinthMarkingClass k = leechHyperbolicCoordinates.symm
      (monsterCo1GeometryBinaryMaskDecode (generatedNinthMarkingMask k)) := by
  apply leechHyperbolicCoordinates.injective
  rw [generatedNinth_marking_class_binary_of_certificate k h]
  simp only [LinearEquiv.apply_symm_apply]

/-- All144 checked coordinate rows identify the complete candidate actual marking-class set. -/
theorem generatedNinth_marked_short_classes_of_coordinate_certificates
    (hcert : ∀ k : Fin 144, GeneratedNinthMarkingCoordinateCertificate k) :
    generatedNinthMarkedShortClasses = Set.range (fun k : Fin 144 =>
      leechHyperbolicCoordinates.symm
        (monsterCo1GeometryBinaryMaskDecode (generatedNinthMarkingMask k))) := by
  rw [← generatedNinth_marking_class_range]
  congr 1
  funext k
  exact generatedNinth_marking_class_of_certificate k (hcert k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
