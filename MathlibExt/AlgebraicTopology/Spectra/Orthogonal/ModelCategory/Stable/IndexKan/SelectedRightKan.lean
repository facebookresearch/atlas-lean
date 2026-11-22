/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.SelectedLocalizations

/-!
# Original native right Kan and its selected Quillen criterion

The genuine weighted-end right Kan functor and the entire original
restriction/right Kan adjunction remain fixed. The level Quillen input
is exactly the original free boundary and horn restriction-image
condition. On selected original localization records, the additional
criterion is exactly that this original right Kan sends every source
Omega diagram to an orthogonal Omega diagram.

Both original records, all families, the original right functor maps,
both Hom functions, unit and counit remain explicit. No right Kan Omega
preservation or native localization existence is inferred from Kan
existence. The actual left Kan descent specializations use the already
proved full native sequential and symmetric Omega restriction laws.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.IndexKan

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open CategoryTheory.Spectra CategoryTheory.Spectra.SpectrumIndexMaps

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev OC := OrthogonalCarrier.{u, v}

variable {A L : Type} [EnrichedCategory PointedCGWH.{u, v} A]

private abbrev AC := EnrichedFunctorCat PointedCGWH.{u, v} A

/-- The full original weighted-end functor with its native source and target types fixed. -/
def originalRan (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    AC.{u, v} (A := A) ⥤ OC.{u, v} := EnrichedFunctorCat.rightKan j

/-- The whole original native right Kan functor and every one of its original maps remain. -/
theorem originalRan_eq (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    originalRan j = EnrichedFunctorCat.rightKan j := rfl

/-- The same actual restriction/right Kan adjunction on the full original native carriers. -/
def originalRanAdjunction (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    EnrichedFunctorCat.restriction j ⊣ originalRan j := EnrichedFunctorCat.rightKanAdjunction j

/-- The entire original end adjunction, with both Hom functions and triangles, is retained. -/
theorem originalRanAdjunction_eq (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    originalRanAdjunction j = EnrichedFunctorCat.rightKanAdjunction j := rfl

/-- The entire native end Hom function is the original weighted-end adjunct. -/
theorem originalRanAdjunction_homEquiv
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (E : OC.{u, v})
    (X : AC.{u, v} (A := A)) :
    (originalRanAdjunction j).homEquiv E X = EnrichedFunctorCat.rightKanHomEquiv j E X :=
  EnrichedFunctorCat.rightKanAdjunction_homEquiv j E X

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

/-- The actual original level Quillen criterion keeps both complete original generator images. -/
theorem originalRanAdjunction_isQuillen_iff
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    (originalRanAdjunction j).IsQuillenAdjunction ↔
      HomotopicalAlgebra.EnrichedProjective.generators (A := O)
          PointedCGWH.realizedBoundaryInclusions.{u, v} ≤
        (cofibrations (AC.{u, v} (A := A))).inverseImage (EnrichedFunctorCat.restriction j) ∧
      HomotopicalAlgebra.EnrichedProjective.generators (A := O)
          PointedCGWH.realizedHornInclusions.{u, v} ≤
        (trivialCofibrations (AC.{u, v} (A := A))).inverseImage
          (EnrichedFunctorCat.restriction j) :=
  rightKan_isQuillen_iff_original_images j

variable (s : NativeStabilizationFamily.{u, v} A L)
  (LC : LeftBousfieldLocalizationData (DerivedLocalMapping.stabilizationArrows s))
  (LO : LeftBousfieldLocalizationData (DerivedLocalMapping.stabilizationArrows orthogonalFamily))

/-- The selected right Kan functor is the same whole original native weighted end. -/
def selectedRan (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    LeftLocalized LC ⥤ LeftLocalized LO :=
  LeftLocalized.rightFunctor LO LC (originalRan j)

/-- The complete second adjunction retains the original selected restriction and right Kan. -/
def selectedRanAdjunction (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    selectedRestriction s LC LO j ⊣ selectedRan s LC LO j :=
  LeftLocalized.adjunction LO LC (originalRanAdjunction j)

/-- Forgetting the selected records retains the entire original right Kan functor. -/
theorem selectedRan_comp_toBase (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    selectedRan s LC LO j ⋙ LeftLocalized.toBase LO =
      LeftLocalized.toBase LC ⋙ originalRan j :=
  LeftLocalized.rightFunctor_comp_toBase LO LC (originalRan j)

/-- Every selected right Kan object is the same original full native weighted end. -/
theorem selectedRan_obj (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : LeftLocalized LC) :
    (LeftLocalized.toBase LO).obj ((selectedRan s LC LO j).obj X) =
      (originalRan j).obj ((LeftLocalized.toBase LC).obj X) := rfl

/-- Every original selected source arrow retains its full original right Kan map. -/
theorem selectedRan_map (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : LeftLocalized LC} (f : X ⟶ Y) :
    (LeftLocalized.toBase LO).map ((selectedRan s LC LO j).map f) =
      (originalRan j).map ((LeftLocalized.toBase LC).map f) := rfl

/-- The second selected unit is the same entire original native end unit. -/
theorem selectedRanAdjunction_unit
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (E : LeftLocalized LO) :
    (LeftLocalized.toBase LO).map ((selectedRanAdjunction s LC LO j).unit.app E) =
      (originalRanAdjunction j).unit.app ((LeftLocalized.toBase LO).obj E) := rfl

/-- The second selected counit retains the unchanged original end counit. -/
theorem selectedRanAdjunction_counit
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (X : LeftLocalized LC) :
    (LeftLocalized.toBase LC).map ((selectedRanAdjunction s LC LO j).counit.app X) =
      (originalRanAdjunction j).counit.app ((LeftLocalized.toBase LC).obj X) := rfl

/-- The complete second forward Hom function retains the actual original end adjunct. -/
theorem selectedRanAdjunction_homEquiv
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (E : LeftLocalized LO) (X : LeftLocalized LC)
    (f : (selectedRestriction s LC LO j).obj E ⟶ X) :
    (LeftLocalized.toBase LO).map ((selectedRanAdjunction s LC LO j).homEquiv E X f) =
      (originalRanAdjunction j).homEquiv ((LeftLocalized.toBase LO).obj E)
        ((LeftLocalized.toBase LC).obj X) ((LeftLocalized.toBase LC).map f) :=
  LeftLocalized.adjunction_homEquiv_toBase LO LC (originalRanAdjunction j) E X f

/-- The second inverse Hom function retains the same full native original inverse adjunct. -/
theorem selectedRanAdjunction_homEquiv_symm
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (E : LeftLocalized LO) (X : LeftLocalized LC)
    (f : E ⟶ (selectedRan s LC LO j).obj X) :
    (LeftLocalized.toBase LC).map (((selectedRanAdjunction s LC LO j).homEquiv E X).symm f) =
      ((originalRanAdjunction j).homEquiv ((LeftLocalized.toBase LO).obj E)
        ((LeftLocalized.toBase LC).obj X)).symm ((LeftLocalized.toBase LO).map f) :=
  LeftLocalized.adjunction_homEquiv_symm_toBase LO LC (originalRanAdjunction j) E X f

/-- Given exactly the original level generator-image conditions, the second Quillen
criterion is preservation of every original native Omega object by the actual right Kan. -/
theorem selectedRanAdjunction_isQuillen_iff
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hImages :
      HomotopicalAlgebra.EnrichedProjective.generators (A := O)
          PointedCGWH.realizedBoundaryInclusions.{u, v} ≤
        (cofibrations (AC.{u, v} (A := A))).inverseImage (EnrichedFunctorCat.restriction j) ∧
      HomotopicalAlgebra.EnrichedProjective.generators (A := O)
          PointedCGWH.realizedHornInclusions.{u, v} ≤
        (trivialCofibrations (AC.{u, v} (A := A))).inverseImage
          (EnrichedFunctorCat.restriction j)) :
    (selectedRanAdjunction s LC LO j).IsQuillenAdjunction ↔
      ∀ X : AC.{u, v} (A := A), NativeK.IsOmega s X →
        NativeK.IsOmega orthogonalFamily ((originalRan j).obj X) := by
  let _ : (originalRanAdjunction j).IsQuillenAdjunction :=
    (originalRanAdjunction_isQuillen_iff j).mpr hImages
  have h := LeftLocalized.isQuillenAdjunction_iff_preservesLocalFibrant LO LC
    (originalRanAdjunction j)
  constructor
  · intro hQ X hX
    exact (DerivedLocalMapping.isLocalFibrant_iff_isOmega orthogonalFamily _).mp
      (h.mp hQ X ((DerivedLocalMapping.isLocalFibrant_iff_isOmega s X).mpr hX))
  · intro hOmega
    apply h.mpr
    intro X hX
    exact (DerivedLocalMapping.isLocalFibrant_iff_isOmega orthogonalFamily _).mpr
      (hOmega X ((DerivedLocalMapping.isLocalFibrant_iff_isOmega s X).mp hX))

end PointedCGWH.Spectra.Orthogonal.IndexKan

namespace PointedCGWH.Spectra.Orthogonal.IndexKan

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open CategoryTheory.Spectra CategoryTheory.Spectra.SpectrumIndexMaps

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

/-- The actual original sequential index adjunction is Quillen whenever its two original
localization records are selected; every native Omega condition is already proved. -/
theorem selectedSequentialAdjunction_isQuillen
    (LS : LeftBousfieldLocalizationData (DerivedLocalMapping.stabilizationArrows
      PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily.{u, v}))
    (LO : LeftBousfieldLocalizationData (DerivedLocalMapping.stabilizationArrows
      orthogonalFamily.{u, v})) :
    (selectedAdjunction PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily
      LS LO sequentialOrthogonalOperatorIndexFunctor).IsQuillenAdjunction :=
  selectedAdjunction_isQuillen PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily
    LS LO sequentialOrthogonalOperatorIndexFunctor
    (fun E hE => (sequentialRestriction_isOmega_iff E).mpr hE)

/-- The unchanged actual symmetric index adjunction satisfies the selected Quillen law
for both full original families, with every native dimension pair retained. -/
theorem selectedSymmetricAdjunction_isQuillen
    (LS : LeftBousfieldLocalizationData (DerivedLocalMapping.stabilizationArrows
      symmetricFamily.{u, v}))
    (LO : LeftBousfieldLocalizationData (DerivedLocalMapping.stabilizationArrows
      orthogonalFamily.{u, v})) :
    (selectedAdjunction symmetricFamily LS LO
      symmetricOrthogonalOperatorIndexFunctor).IsQuillenAdjunction :=
  selectedAdjunction_isQuillen symmetricFamily LS LO symmetricOrthogonalOperatorIndexFunctor
    (fun E hE => (symmetricRestriction_isOmega_iff E).mpr hE)

end PointedCGWH.Spectra.Orthogonal.IndexKan
