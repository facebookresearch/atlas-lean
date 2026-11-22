/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.LocalizingImages
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Quillen

/-!
# Quillen laws for selected original native index localizations

The selected localization records remain explicit premises. Their
families are the unchanged original native stabilization Arrow functions.
The complete original Lan/restriction adjunction, including every map,
Hom function, unit, counit and triangle, is retained on those selected
carriers. Its Quillen criterion is exactly preservation of the original
full-family Omega objects by the actual restriction.

The proved sequential and symmetric restriction laws discharge that
criterion whenever the two original localization records are selected.
This supplies no native localization-existence theorem and assumes no
source comparison or stable Quillen equivalence.
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

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

variable (s : NativeStabilizationFamily.{u, v} A L)
  (LC : LeftBousfieldLocalizationData (DerivedLocalMapping.stabilizationArrows s))
  (LO : LeftBousfieldLocalizationData
    (DerivedLocalMapping.stabilizationArrows orthogonalFamily))

/-- The selected left functor retains the entire original raw coend Lan. -/
def selectedLan (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    LeftLocalized LC ⥤ LeftLocalized LO :=
  LeftLocalized.leftFunctor LC LO (originalLan j)

/-- The selected right functor retains the complete original native restriction. -/
def selectedRestriction (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    LeftLocalized LO ⥤ LeftLocalized LC :=
  LeftLocalized.rightFunctor LC LO (EnrichedFunctorCat.restriction j)

/-- The entire original adjunction is retained with both selected localization families. -/
def selectedAdjunction (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    selectedLan s LC LO j ⊣ selectedRestriction s LC LO j :=
  LeftLocalized.adjunction LC LO (originalAdjunction j)

/-- The whole original left functor remains after forgetting the selected localization. -/
theorem selectedLan_comp_toBase (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    selectedLan s LC LO j ⋙ LeftLocalized.toBase LO =
      LeftLocalized.toBase LC ⋙ originalLan j :=
  LeftLocalized.leftFunctor_comp_toBase LC LO (originalLan j)

/-- The whole original right functor remains with every original source and target action. -/
theorem selectedRestriction_comp_toBase
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    selectedRestriction s LC LO j ⋙ LeftLocalized.toBase LC =
      LeftLocalized.toBase LO ⋙ EnrichedFunctorCat.restriction j :=
  LeftLocalized.rightFunctor_comp_toBase LC LO (EnrichedFunctorCat.restriction j)

/-- Every left object is the same actual original coend object. -/
theorem selectedLan_obj (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : LeftLocalized LC) :
    (LeftLocalized.toBase LO).obj ((selectedLan s LC LO j).obj X) =
      (originalLan j).obj ((LeftLocalized.toBase LC).obj X) := rfl

/-- Every right object retains the complete original restricted native diagram. -/
theorem selectedRestriction_obj (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (E : LeftLocalized LO) :
    (LeftLocalized.toBase LC).obj ((selectedRestriction s LC LO j).obj E) =
      (EnrichedFunctorCat.restriction j).obj ((LeftLocalized.toBase LO).obj E) := rfl

/-- The complete original left map is retained on every actual selected-carrier arrow. -/
theorem selectedLan_map (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : LeftLocalized LC} (f : X ⟶ Y) :
    (LeftLocalized.toBase LO).map ((selectedLan s LC LO j).map f) =
      (originalLan j).map ((LeftLocalized.toBase LC).map f) := rfl

/-- Every original right map is the same full unit-graded restriction transformation. -/
theorem selectedRestriction_map (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {E E' : LeftLocalized LO} (f : E ⟶ E') :
    (LeftLocalized.toBase LC).map ((selectedRestriction s LC LO j).map f) =
      (EnrichedFunctorCat.restriction j).map ((LeftLocalized.toBase LO).map f) := rfl

/-- Every original unit is the same actual native coend/restriction unit. -/
theorem selectedAdjunction_unit
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (X : LeftLocalized LC) :
    (LeftLocalized.toBase LC).map ((selectedAdjunction s LC LO j).unit.app X) =
      (originalAdjunction j).unit.app ((LeftLocalized.toBase LC).obj X) := rfl

/-- Every original counit is the unchanged full native coend counit. -/
theorem selectedAdjunction_counit
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (E : LeftLocalized LO) :
    (LeftLocalized.toBase LO).map ((selectedAdjunction s LC LO j).counit.app E) =
      (originalAdjunction j).counit.app ((LeftLocalized.toBase LO).obj E) := rfl

/-- The whole forward Hom function is the original actual native adjunct. -/
theorem selectedAdjunction_homEquiv
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : LeftLocalized LC) (E : LeftLocalized LO)
    (f : (selectedLan s LC LO j).obj X ⟶ E) :
    (LeftLocalized.toBase LC).map ((selectedAdjunction s LC LO j).homEquiv X E f) =
      (originalAdjunction j).homEquiv ((LeftLocalized.toBase LC).obj X)
        ((LeftLocalized.toBase LO).obj E) ((LeftLocalized.toBase LO).map f) :=
  LeftLocalized.adjunction_homEquiv_toBase LC LO (originalAdjunction j) X E f

/-- The full inverse Hom function retains the same original native inverse adjunct. -/
theorem selectedAdjunction_homEquiv_symm
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : LeftLocalized LC) (E : LeftLocalized LO)
    (f : X ⟶ (selectedRestriction s LC LO j).obj E) :
    (LeftLocalized.toBase LO).map (((selectedAdjunction s LC LO j).homEquiv X E).symm f) =
      ((originalAdjunction j).homEquiv ((LeftLocalized.toBase LC).obj X)
        ((LeftLocalized.toBase LO).obj E)).symm ((LeftLocalized.toBase LC).map f) :=
  LeftLocalized.adjunction_homEquiv_symm_toBase LC LO (originalAdjunction j) X E f

/-- Every original source arrow retains the entire same unit naturality square. -/
theorem selectedAdjunction_unit_naturality
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : LeftLocalized LC} (f : X ⟶ Y) :
    f ≫ (selectedAdjunction s LC LO j).unit.app Y =
      (selectedAdjunction s LC LO j).unit.app X ≫
        (selectedRestriction s LC LO j).map ((selectedLan s LC LO j).map f) :=
  (selectedAdjunction s LC LO j).unit.naturality f

/-- Every original target arrow retains the full unchanged counit naturality square. -/
theorem selectedAdjunction_counit_naturality
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {E E' : LeftLocalized LO} (f : E ⟶ E') :
    (selectedLan s LC LO j).map ((selectedRestriction s LC LO j).map f) ≫
        (selectedAdjunction s LC LO j).counit.app E' =
      (selectedAdjunction s LC LO j).counit.app E ≫ f :=
  (selectedAdjunction s LC LO j).counit.naturality f

/-- The complete original left triangle holds on each selected original source. -/
theorem selectedAdjunction_left_triangle
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (X : LeftLocalized LC) :
    (selectedLan s LC LO j).map ((selectedAdjunction s LC LO j).unit.app X) ≫
        (selectedAdjunction s LC LO j).counit.app ((selectedLan s LC LO j).obj X) =
      𝟙 ((selectedLan s LC LO j).obj X) :=
  (selectedAdjunction s LC LO j).left_triangle_components X

/-- The actual full original right triangle holds at every selected target. -/
theorem selectedAdjunction_right_triangle
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (E : LeftLocalized LO) :
    (selectedAdjunction s LC LO j).unit.app ((selectedRestriction s LC LO j).obj E) ≫
        (selectedRestriction s LC LO j).map ((selectedAdjunction s LC LO j).counit.app E) =
      𝟙 ((selectedRestriction s LC LO j).obj E) :=
  (selectedAdjunction s LC LO j).right_triangle_components E

/-- The exact Quillen criterion is the full native original Omega restriction condition. -/
theorem selectedAdjunction_isQuillen_iff
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    (selectedAdjunction s LC LO j).IsQuillenAdjunction ↔
      ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
        NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E) := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  have h := LeftLocalized.isQuillenAdjunction_iff_preservesLocalFibrant LC LO
    (originalAdjunction j)
  constructor
  · intro hQ E hE
    exact (DerivedLocalMapping.isLocalFibrant_iff_isOmega s _).mp
      (h.mp hQ E ((DerivedLocalMapping.isLocalFibrant_iff_isOmega orthogonalFamily E).mpr hE))
  · intro hOmega
    apply h.mpr
    intro E hE
    exact (DerivedLocalMapping.isLocalFibrant_iff_isOmega s _).mpr
      (hOmega E ((DerivedLocalMapping.isLocalFibrant_iff_isOmega orthogonalFamily E).mp hE))

/-- The actual full native Omega restriction law constructs the selected Quillen adjunction. -/
theorem selectedAdjunction_isQuillen
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hOmega : ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
      NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E)) :
    (selectedAdjunction s LC LO j).IsQuillenAdjunction :=
  (selectedAdjunction_isQuillen_iff s LC LO j).mpr hOmega

/-- Every original cofibration is preserved on the selected original carriers. -/
theorem selectedLan_preservesCofibrations
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    PreservesCofibrations (selectedLan s LC LO j) := by
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  exact LeftLocalized.leftFunctor_preservesCofibrations LC LO (originalAdjunction j)

/-- The full Omega restriction law preserves every selected original trivial cofibration. -/
theorem selectedLan_preservesTrivialCofibrations
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hOmega : ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
      NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E)) :
    PreservesTrivialCofibrations (selectedLan s LC LO j) :=
  (selectedAdjunction_isQuillen s LC LO j hOmega).preservesTrivialCofibrations

/-- Every selected original fibration retains its complete restricted native map. -/
theorem selectedRestriction_preservesFibrations
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hOmega : ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
      NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E)) :
    PreservesFibrations (selectedRestriction s LC LO j) := by
  let _ : (selectedAdjunction s LC LO j).IsQuillenAdjunction :=
    selectedAdjunction_isQuillen s LC LO j hOmega
  exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := selectedAdjunction s LC LO j)

/-- All selected original trivial fibrations are preserved by the unchanged restriction. -/
theorem selectedRestriction_preservesTrivialFibrations
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (hOmega : ∀ E : OC.{u, v}, NativeK.IsOmega orthogonalFamily E →
      NativeK.IsOmega s ((EnrichedFunctorCat.restriction j).obj E)) :
    PreservesTrivialFibrations (selectedRestriction s LC LO j) := by
  let _ : (selectedAdjunction s LC LO j).IsQuillenAdjunction :=
    selectedAdjunction_isQuillen s LC LO j hOmega
  exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
    (adj := selectedAdjunction s LC LO j)

/-- The whole original native Omega test class is the selected weak class on base arrows. -/
theorem selectedWeak_iff_omegaTests {X Y : AC.{u, v} (A := A)} (f : X ⟶ Y) :
    weakEquivalences (LeftLocalized LC) ((LeftLocalized.ofBase LC).map f) ↔
      NativeK.omegaTests s f := by
  change localEquivalences (DerivedLocalMapping.stabilizationArrows s) f ↔ NativeK.omegaTests s f
  rw [DerivedLocalMapping.localEquivalences_eq_omegaTests]

/-- Selected fibrancy is exactly the same original full-family native Omega condition. -/
theorem selectedFibrant_iff_isOmega (X : LeftLocalized LC) :
    IsFibrant X ↔ NativeK.IsOmega s ((LeftLocalized.toBase LC).obj X) :=
  (LeftLocalized.fibrant_iff LC X).trans (DerivedLocalMapping.isLocalFibrant_iff_isOmega s X.1)

end PointedCGWH.Spectra.Orthogonal.IndexKan
