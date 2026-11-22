/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeKan
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Replacement
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialIndexOmegaTransport

/-!
# Original native level Kan records for orthogonal targets

The actual weighted coend and end adjunctions use the unchanged native
orthogonal carrier. The existing projective Kan laws are interpreted
in the caller's original native level models at the same realized
cardinal and bottom. Every index Hom action remains the original one.

Actual restriction and original Lan after the original Q descend to the
original level homotopy categories. Their full object and represented-map
functions retain the original restriction, Q and Lan maps. Right Kan's
level Quillen criterion keeps the original free boundary and horn images.
No stable model or native comparison outcome is a prerequisite.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.IndexKan

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev OC := OrthogonalCarrier.{u, v}

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

private abbrev AC := EnrichedFunctorCat PointedCGWH.{u, v} A

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev HA := toHomotopyCategory (AC.{u, v} (A := A))
private abbrev HO := toHomotopyCategory OC.{u, v}

/-- The genuine original coend Lan adjunction is level Quillen for
the same caller-bottom native level models. -/
theorem leftKan_isQuillen (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    (EnrichedFunctorCat.leftKanRestrictionAdjunction j).IsQuillenAdjunction := by
  have h := HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanRestriction_isQuillen j
  simpa only [HomotopicalAlgebra.EnrichedProjective.Native.Construction.modelCategory_eq_native
    (B := B)] using h

/-- The entire original coend functor, with its source and target types fixed. -/
def originalLan (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    AC.{u, v} (A := A) ⥤ OC.{u, v} :=
  EnrichedFunctorCat.leftKan j

omit B in
/-- This is the same whole original native Lan, including all its original map fields. -/
theorem originalLan_eq (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    originalLan j = EnrichedFunctorCat.leftKan j := rfl

omit B in
/-- Every original Lan object is the genuine enriched weighted coend object. -/
theorem originalLan_obj (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) :
    (originalLan j).obj X = EnrichedFunctorCat.leftKanObject j X := rfl

omit B in
/-- The whole functor equality identifies every original enriched coend map,
with both actual source and target object identifications retained. -/
theorem originalLan_map (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} (f : X ⟶ Y) :
    (originalLan j).map f =
      eqToHom (Functor.congr_obj (originalLan_eq j) X) ≫
        (EnrichedFunctorCat.leftKan j).map f ≫
        eqToHom (Functor.congr_obj (originalLan_eq j) Y).symm :=
  Functor.congr_hom (originalLan_eq j) f

/-- The original coend/restriction adjunction on its fixed full native carrier types. -/
def originalAdjunction (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    originalLan j ⊣ EnrichedFunctorCat.restriction j :=
  EnrichedFunctorCat.leftKanRestrictionAdjunction j

omit B in
/-- The whole original adjunction retains the unchanged Hom functions, unit and counit. -/
theorem originalAdjunction_eq (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    originalAdjunction j = EnrichedFunctorCat.leftKanRestrictionAdjunction j := rfl

/-- The same original level Quillen record applies to the fixed native Lan functor. -/
theorem originalAdjunction_isQuillen (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    (originalAdjunction j).IsQuillenAdjunction :=
  leftKan_isQuillen j

/-- The actual right Kan adjunction is level Quillen precisely for
the original full free boundary and horn restriction-image conditions. -/
theorem rightKan_isQuillen_iff_original_images
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    (EnrichedFunctorCat.rightKanAdjunction j).IsQuillenAdjunction ↔
      HomotopicalAlgebra.EnrichedProjective.generators (A := O)
          PointedCGWH.realizedBoundaryInclusions.{u, v} ≤
        (cofibrations (AC.{u, v} (A := A))).inverseImage
          (EnrichedFunctorCat.restriction j) ∧
      HomotopicalAlgebra.EnrichedProjective.generators (A := O)
          PointedCGWH.realizedHornInclusions.{u, v} ≤
        (trivialCofibrations (AC.{u, v} (A := A))).inverseImage
          (EnrichedFunctorCat.restriction j) := by
  have h := HomotopicalAlgebra.EnrichedProjective.Native.Kan.rightKan_isQuillen_iff_generators j
  simpa only [HomotopicalAlgebra.EnrichedProjective.Native.Construction.modelCategory_eq_native
    (B := B)] using h

/-- Every original level weak map restricts by its unchanged full native component maps. -/
theorem restriction_levelWeak (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : OC.{u, v}} (f : X ⟶ Y) (hf : weakEquivalences OC.{u, v} f) :
    weakEquivalences (AC.{u, v} (A := A)) ((EnrichedFunctorCat.restriction j).map f) := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq] at hf ⊢
  rw [EvaluationTransfer.evaluationProperty_iff] at hf ⊢
  intro a
  change weakEquivalences PointedCGWH.{u, v}
    (component (EnrichedFunctorCat.restrictionMap j f) a)
  rw [EnrichedFunctorCat.restrictionMap_component]
  exact hf (j.obj a)

/-- The actual full original restriction inverts the original level weak arrows in Ho. -/
theorem restriction_inverts (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    (weakEquivalences OC.{u, v}).IsInvertedBy (EnrichedFunctorCat.restriction j ⋙ HA) := by
  intro X Y f hf
  exact Localization.inverts HA (weakEquivalences (AC.{u, v} (A := A)))
    ((EnrichedFunctorCat.restriction j).map f) (restriction_levelWeak j f hf)

/-- The literal original restriction descends to the two original native level Ho categories. -/
def restrictionHoFunctor (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    HomotopyCategory OC.{u, v} ⥤ HomotopyCategory (AC.{u, v} (A := A)) :=
  Localization.Construction.lift (EnrichedFunctorCat.restriction j ⋙ HA) (restriction_inverts j)

/-- The entire descended restriction retains its whole original source functor. -/
theorem restrictionHoFunctor_fac (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    HO ⋙ restrictionHoFunctor j = EnrichedFunctorCat.restriction j ⋙ HA :=
  Localization.Construction.fac (EnrichedFunctorCat.restriction j ⋙ HA) (restriction_inverts j)

/-- Every actual original restriction object is retained without another replacement. -/
theorem restrictionHoFunctor_obj (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : OC.{u, v}) :
    (restrictionHoFunctor j).obj (HO.obj X) = HA.obj ((EnrichedFunctorCat.restriction j).obj X) :=
  rfl

/-- Every represented map is the same entire original restricted native map. -/
theorem restrictionHoFunctor_map (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : OC.{u, v}} (f : X ⟶ Y) :
    (restrictionHoFunctor j).map (HO.map f) = HA.map ((EnrichedFunctorCat.restriction j).map f) :=
  Functor.congr_hom (restrictionHoFunctor_fac j) f

/-- The source's unchanged original I replacement is retained before the original Lan. -/
abbrev originalQ : (AC.{u, v} (A := A)) ⥤ (AC.{u, v} (A := A)) :=
  Replacement.cofibrantReplacement (B := B) (A := A)

/-- Its whole original same-cardinal counit is the actual source replacement map. -/
abbrev originalQCounit : originalQ.{u, v} (A := A) ⟶ 𝟭 (AC.{u, v} (A := A)) :=
  Replacement.cofibrantReplacementCounit (B := B) (A := A)

/-- The full original source I record makes each original Q object cofibrant. -/
theorem originalQ_isCofibrant (X : AC.{u, v} (A := A)) :
    IsCofibrant ((originalQ (A := A)).obj X) :=
  Replacement.isCofibrant_cofibrantReplacement (B := B) (A := A) X

/-- The unchanged original Q counit retains its actual original level weakness. -/
theorem originalQCounit_levelWeak (X : AC.{u, v} (A := A)) :
    weakEquivalences (AC.{u, v} (A := A)) ((originalQCounit (A := A)).app X) :=
  Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) (A := A) X

/-- Every original source Q map preserves the same full original level weak class. -/
theorem originalQ_map_levelWeak {X Y : AC.{u, v} (A := A)} (f : X ⟶ Y)
    (hf : weakEquivalences (AC.{u, v} (A := A)) f) :
    weakEquivalences (AC.{u, v} (A := A)) ((originalQ (A := A)).map f) :=
  Replacement.cofibrantReplacement_map_mem_weakEquivalences (B := B) (A := A) f hf

/-- The actual original Lan after the unchanged original Q functor. -/
def prolongedQ (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    AC.{u, v} (A := A) ⥤ OC.{u, v} :=
  originalQ (A := A) ⋙ originalLan j

/-- The whole functor is exactly the original source Q followed by the original coend Lan. -/
theorem prolongedQ_eq (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    prolongedQ j = originalQ (A := A) ⋙ EnrichedFunctorCat.leftKan j := rfl

/-- Every original prolonged Q object retains the same source Q and original coend Lan. -/
theorem prolongedQ_obj (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : AC.{u, v} (A := A)) :
    (prolongedQ j).obj X = (originalLan j).obj ((originalQ (A := A)).obj X) := rfl

/-- Every whole original source map retains both the actual Q and original Lan maps. -/
theorem prolongedQ_map (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : AC.{u, v} (A := A)} (f : X ⟶ Y) :
    (prolongedQ j).map f = (originalLan j).map ((originalQ (A := A)).map f) := rfl

/-- Original Q and the actual native level Quillen law make Lan Q
invert every original source level weak map in the unchanged target Ho. -/
theorem prolongedQ_inverts (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    (weakEquivalences (AC.{u, v} (A := A))).IsInvertedBy (prolongedQ j ⋙ HO) := by
  intro X Y f hf
  let _ : (originalAdjunction j).IsQuillenAdjunction := originalAdjunction_isQuillen j
  let _ : IsCofibrant ((originalQ (A := A)).obj X) := originalQ_isCofibrant X
  let _ : IsCofibrant ((originalQ (A := A)).obj Y) := originalQ_isCofibrant Y
  let _ : WeakEquivalence ((originalQ (A := A)).map f) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (originalQ_map_levelWeak f hf)
  have h : WeakEquivalence ((originalLan j).map ((originalQ (A := A)).map f)) :=
    CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := originalAdjunction j) ((originalQ (A := A)).map f)
  exact Localization.inverts HO (weakEquivalences OC.{u, v})
    ((originalLan j).map ((originalQ (A := A)).map f)) h.mem

/-- The original Lan Q descends through the original source localization
with its unchanged entire original source and target functions. -/
def prolongedHoFunctor (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    HomotopyCategory (AC.{u, v} (A := A)) ⥤ HomotopyCategory OC.{u, v} :=
  Localization.Construction.lift (prolongedQ j ⋙ HO) (prolongedQ_inverts j)

/-- The whole composite is the same full original source Lan Q functor. -/
theorem prolongedHoFunctor_fac (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) :
    HA ⋙ prolongedHoFunctor j = prolongedQ j ⋙ HO :=
  Localization.Construction.fac (prolongedQ j ⋙ HO) (prolongedQ_inverts j)

/-- Every original source object has the literal original Lan Q image in target Ho. -/
theorem prolongedHoFunctor_obj (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (X : (AC.{u, v} (A := A))) :
    (prolongedHoFunctor j).obj (HA.obj X) = HO.obj ((prolongedQ j).obj X) := rfl

/-- Every represented source arrow has the literal original Lan Q map in target Ho. -/
theorem prolongedHoFunctor_map (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    {X Y : (AC.{u, v} (A := A))} (f : X ⟶ Y) :
    (prolongedHoFunctor j).map (HA.map f) = HO.map ((prolongedQ j).map f) :=
  Functor.congr_hom (prolongedHoFunctor_fac j) f

end PointedCGWH.Spectra.Orthogonal.IndexKan
