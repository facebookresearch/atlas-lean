/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedEquivalence
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.LeftRightDerivedAdjunction

/-!
# The two original canonical derived sphere-conversion equivalences

The actual original conversion and inverse preserve weak equivalences on every object.
Both canonical derived adjunctions therefore give equivalences of their original localizations.
Their functors, full comparison maps, units and counits remain the given canonical values.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.Spectra.Symmetric.LeftRightNativeModel

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

@[instance_reducible]
private def sourceLeftModel : ModelCategory PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

@[instance_reducible]
private def sourceRightModel : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
    PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}

attribute [local instance] sourceLeftModel sourceRightModel
  toRight_isQuillenAdjunction toLeft_isQuillenAdjunction


/-- Every original weak equivalence maps through the entire genuine forward conversion. -/
theorem toRight_allWeakMaps : (weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) ≤
  ((weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).inverseImage
  (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).functor := by
  intro X Y f hf
  exact (toRight_weakEquivalences_iff f).mpr hf

/-- The actual original inverse maps the complete weak class back to the original left model. -/
theorem toLeft_allWeakMaps : (weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) ≤
  ((weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).inverseImage
  (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).inverse := by
  intro X Y f hf
  exact (toLeft_weakEquivalences_iff f).mpr hf

/-- The whole original forward left-derived comparison is invertible on all objects. -/
theorem toRightDerived_leftComparison_isIso : IsIso (toRightDerivedAdjunctionData.{u,
  v}).leftComparison :=
  quillenDerived_leftComparison_isIso
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).toAdjunction
    toRight_allWeakMaps

/-- The original forward right-derived comparison is an isomorphism of entire functors. -/
theorem toRightDerived_rightComparison_isIso : IsIso (toRightDerivedAdjunctionData.{u,
  v}).rightComparison :=
  quillenDerived_rightComparison_isIso
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).toAdjunction
    toLeft_allWeakMaps

/-- The actual inverse left comparison is invertible on every original right object. -/
theorem toLeftDerived_leftComparison_isIso : IsIso (toLeftDerivedAdjunctionData.{u,
  v}).leftComparison :=
  quillenDerived_leftComparison_isIso
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).symm.toAdjunction
    toLeft_allWeakMaps

/-- The actual inverse right comparison retains the entire original forward functor. -/
theorem toLeftDerived_rightComparison_isIso : IsIso (toLeftDerivedAdjunctionData.{u,
  v}).rightComparison :=
  quillenDerived_rightComparison_isIso
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).symm.toAdjunction
    toRight_allWeakMaps

/-- The exact original forward left comparison, as a whole natural isomorphism. -/
def toRightDerivedLeftComparisonIso :
    ((weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q ⋙
      (toRightDerivedAdjunctionData.{u, v}).leftDerived ≅
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).functor ⋙
      ((weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q := by
  let _ : IsIso (toRightDerivedAdjunctionData.{u, v}).leftComparison :=
    toRightDerived_leftComparison_isIso
  exact asIso (toRightDerivedAdjunctionData.{u, v}).leftComparison

/-- The entire given forward right comparison, with its original map. -/
def toRightDerivedRightComparisonIso :
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).inverse ⋙ ((weakEquivalences
      PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q ≅ ((weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q ⋙ (toRightDerivedAdjunctionData.{u,
      v}).rightDerived := by
  let _ : IsIso (toRightDerivedAdjunctionData.{u, v}).rightComparison :=
    toRightDerived_rightComparison_isIso
  exact asIso (toRightDerivedAdjunctionData.{u, v}).rightComparison

/-- The whole original inverse left comparison is the same given natural transformation. -/
def toLeftDerivedLeftComparisonIso :
    ((weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q ⋙
      (toLeftDerivedAdjunctionData.{u, v}).leftDerived ≅
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).inverse ⋙
      ((weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q := by
  let _ : IsIso (toLeftDerivedAdjunctionData.{u, v}).leftComparison :=
    toLeftDerived_leftComparison_isIso
  exact asIso (toLeftDerivedAdjunctionData.{u, v}).leftComparison

/-- The full inverse right comparison keeps the original forward conversion. -/
def toLeftDerivedRightComparisonIso :
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).functor ⋙ ((weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q ≅ ((weakEquivalences
      PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q ⋙ (toLeftDerivedAdjunctionData.{u, v}).rightDerived
      := by
  let _ : IsIso (toLeftDerivedAdjunctionData.{u, v}).rightComparison :=
    toLeftDerived_rightComparison_isIso
  exact asIso (toLeftDerivedAdjunctionData.{u, v}).rightComparison

/-- The first whole forward comparison uses exactly the original derived counit map. -/
theorem toRightDerivedLeftComparisonIso_hom :
    toRightDerivedLeftComparisonIso.{u, v}.hom = (toRightDerivedAdjunctionData.{u,
      v}).leftComparison := rfl

/-- The other whole forward comparison keeps exactly the original derived unit map. -/
theorem toRightDerivedRightComparisonIso_hom :
    toRightDerivedRightComparisonIso.{u, v}.hom = (toRightDerivedAdjunctionData.{u,
      v}).rightComparison := rfl

/-- The whole inverse left comparison retains the complete given original map. -/
theorem toLeftDerivedLeftComparisonIso_hom :
    toLeftDerivedLeftComparisonIso.{u, v}.hom = (toLeftDerivedAdjunctionData.{u,
      v}).leftComparison := rfl

/-- The whole inverse right comparison keeps the complete original forward map. -/
theorem toLeftDerivedRightComparisonIso_hom :
    toLeftDerivedRightComparisonIso.{u, v}.hom = (toLeftDerivedAdjunctionData.{u,
      v}).rightComparison := rfl

/-- The original forward canonical derived adjunction, as an equivalence of its localizations. -/
def toRightCanonicalDerivedEquivalence : ((weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u,
  v})).Localization ≌ ((weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u,
  v})).Localization :=
  homotopicalQuillenDerivedEquivalence
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).toAdjunction
    toRight_allWeakMaps toLeft_allWeakMaps

/-- The original inverse canonical derived adjunction, retaining its two given total functors. -/
def toLeftCanonicalDerivedEquivalence : ((weakEquivalences
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Localization ≌ ((weakEquivalences
  PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Localization :=
  homotopicalQuillenDerivedEquivalence
    (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).symm.toAdjunction
    toLeft_allWeakMaps toRight_allWeakMaps

/-- The complete forward equivalence functor is the actual original total left derived value. -/
theorem toRightCanonicalDerivedEquivalence_functor :
    toRightCanonicalDerivedEquivalence.{u, v}.functor = (toRightDerivedAdjunctionData.{u,
      v}).leftDerived := rfl

/-- Its whole inverse is the original canonical total right derived value. -/
theorem toRightCanonicalDerivedEquivalence_inverse :
    toRightCanonicalDerivedEquivalence.{u, v}.inverse = (toRightDerivedAdjunctionData.{u,
      v}).rightDerived := rfl

/-- The original forward unit is unchanged as a full natural transformation. -/
theorem toRightCanonicalDerivedEquivalence_unit_hom :
    toRightCanonicalDerivedEquivalence.{u, v}.unitIso.hom = (toRightDerivedAdjunctionData.{u,
      v}).adjunction.unit := rfl

/-- The entire forward counit is the actual original derived-adjunction counit. -/
theorem toRightCanonicalDerivedEquivalence_counit_hom :
    toRightCanonicalDerivedEquivalence.{u, v}.counitIso.hom = (toRightDerivedAdjunctionData.{u,
      v}).adjunction.counit := rfl

/-- The entire inverse equivalence functor keeps the original inverse left-derived choice. -/
theorem toLeftCanonicalDerivedEquivalence_functor :
    toLeftCanonicalDerivedEquivalence.{u, v}.functor = (toLeftDerivedAdjunctionData.{u,
      v}).leftDerived := rfl

/-- Its full inverse is the given original inverse right-derived choice. -/
theorem toLeftCanonicalDerivedEquivalence_inverse :
    toLeftCanonicalDerivedEquivalence.{u, v}.inverse = (toLeftDerivedAdjunctionData.{u,
      v}).rightDerived := rfl

/-- The original inverse derived unit is the same complete natural transformation. -/
theorem toLeftCanonicalDerivedEquivalence_unit_hom :
    toLeftCanonicalDerivedEquivalence.{u, v}.unitIso.hom = (toLeftDerivedAdjunctionData.{u,
      v}).adjunction.unit := rfl

/-- The original inverse derived counit remains the actual given complete map. -/
theorem toLeftCanonicalDerivedEquivalence_counit_hom :
    toLeftCanonicalDerivedEquivalence.{u, v}.counitIso.hom = (toLeftDerivedAdjunctionData.{u,
      v}).adjunction.counit := rfl

/-- The whole forward unit retains its original conversion-unit factorization. -/
theorem toRightCanonicalDerivedEquivalence_unit_fac (X : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    toRightCanonicalDerivedEquivalence.unitIso.hom.app (((weakEquivalences
      PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q.obj X) ≫
        (toRightDerivedAdjunctionData.{u, v}).rightDerived.map ((toRightDerivedAdjunctionData.{u,
          v}).leftComparison.app X) =
      ((weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q.map
        ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).unitIso.hom.app X) ≫
        (toRightDerivedAdjunctionData.{u, v}).rightComparison.app
        ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).functor.obj X) :=
  quillenDerived_unit_fac (SymmetricRightModulePresentation.sphereModuleEquivalence.{u,
    v}).toAdjunction X

/-- The actual entire forward counit keeps the original conversion-counit factorization. -/
theorem toRightCanonicalDerivedEquivalence_counit_fac (Y :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    (toRightDerivedAdjunctionData.{u, v}).leftDerived.map ((toRightDerivedAdjunctionData.{u,
      v}).rightComparison.app Y) ≫
        toRightCanonicalDerivedEquivalence.counitIso.hom.app (((weakEquivalences
          PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q.obj Y) =
      (toRightDerivedAdjunctionData.{u, v}).leftComparison.app
        ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).inverse.obj Y) ≫
        ((weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q.map
        ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).counitIso.hom.app Y) :=
  quillenDerived_counit_fac (SymmetricRightModulePresentation.sphereModuleEquivalence.{u,
    v}).toAdjunction Y

/-- The whole inverse unit retains the same actual inverse-conversion unit. -/
theorem toLeftCanonicalDerivedEquivalence_unit_fac (Y :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    toLeftCanonicalDerivedEquivalence.unitIso.hom.app (((weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q.obj Y) ≫
        (toLeftDerivedAdjunctionData.{u, v}).rightDerived.map ((toLeftDerivedAdjunctionData.{u,
          v}).leftComparison.app Y) =
      ((weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q.map
        ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).symm.unitIso.hom.app Y)
        ≫
        (toLeftDerivedAdjunctionData.{u, v}).rightComparison.app
          ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).inverse.obj Y) :=
  quillenDerived_unit_fac (SymmetricRightModulePresentation.sphereModuleEquivalence.{u,
    v}).symm.toAdjunction Y

/-- The actual inverse counit has the original full inverse-conversion counit equation. -/
theorem toLeftCanonicalDerivedEquivalence_counit_fac (X : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) :
    (toLeftDerivedAdjunctionData.{u, v}).leftDerived.map ((toLeftDerivedAdjunctionData.{u,
      v}).rightComparison.app X) ≫
        toLeftCanonicalDerivedEquivalence.counitIso.hom.app (((weakEquivalences
          PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q.obj X) =
      (toLeftDerivedAdjunctionData.{u, v}).leftComparison.app
        ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).functor.obj X) ≫
        ((weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q.map
          ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u,
          v}).symm.counitIso.hom.app X) :=
  quillenDerived_counit_fac (SymmetricRightModulePresentation.sphereModuleEquivalence.{u,
    v}).symm.toAdjunction X

/-- Every original left map retains the full canonical forward left-comparison square. -/
theorem toRightDerived_leftComparison_naturality
    {X Y : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : X ⟶ Y) :
    (toRightDerivedAdjunctionData.{u, v}).leftDerived.map (((weakEquivalences
      PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q.map f) ≫ (toRightDerivedAdjunctionData.{u,
      v}).leftComparison.app Y =
      (toRightDerivedAdjunctionData.{u, v}).leftComparison.app X ≫ ((weakEquivalences
        PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q.map
        ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).functor.map f) :=
  (toRightDerivedAdjunctionData.{u, v}).leftComparison.naturality f

/-- Every original right map keeps the entire original forward right-comparison square. -/
theorem toRightDerived_rightComparison_naturality
    {X Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : X ⟶ Y) :
    ((weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q.map
      ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).inverse.map f) ≫
      (toRightDerivedAdjunctionData.{u, v}).rightComparison.app Y =
      (toRightDerivedAdjunctionData.{u, v}).rightComparison.app X ≫
        (toRightDerivedAdjunctionData.{u, v}).rightDerived.map (((weakEquivalences
        PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q.map f) :=
  (toRightDerivedAdjunctionData.{u, v}).rightComparison.naturality f

/-- The original inverse left comparison is natural on whole right-module arrows. -/
theorem toLeftDerived_leftComparison_naturality
    {X Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : X ⟶ Y) :
    (toLeftDerivedAdjunctionData.{u, v}).leftDerived.map (((weakEquivalences
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q.map f) ≫
        (toLeftDerivedAdjunctionData.{u,
      v}).leftComparison.app Y =
      (toLeftDerivedAdjunctionData.{u, v}).leftComparison.app X ≫ ((weakEquivalences
        PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q.map
        ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).inverse.map f) :=
  (toLeftDerivedAdjunctionData.{u, v}).leftComparison.naturality f

/-- The entire inverse right comparison keeps every given original left-module arrow. -/
theorem toLeftDerived_rightComparison_naturality
    {X Y : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : X ⟶ Y) :
    ((weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})).Q.map
      ((SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).functor.map f) ≫
      (toLeftDerivedAdjunctionData.{u, v}).rightComparison.app Y =
      (toLeftDerivedAdjunctionData.{u, v}).rightComparison.app X ≫
        (toLeftDerivedAdjunctionData.{u, v}).rightDerived.map (((weakEquivalences
        PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})).Q.map f) :=
  (toLeftDerivedAdjunctionData.{u, v}).rightComparison.naturality f

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel

/-!
The native consumers below use the canonical spectrum carrier and its
level model, with the complete original conversion conjugated by the
proved source/operator equivalences.
-/

namespace PointedCGWH.Spectra.Symmetric.LeftRightNativeModel.Canonical

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction


attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel
  toRight_isQuillenAdjunction toLeft_isQuillenAdjunction


/-- Every original weak equivalence maps through the entire genuine forward conversion. -/
theorem toRight_allWeakMaps : (weakEquivalences Spectrum.{u, v}) ≤
  ((weakEquivalences Spectrum.{u, v})).inverseImage
  (carrierEquivalence.{u, v}).functor := by
  intro X Y f hf
  exact (toRight_weakEquivalences_iff f).mpr hf

/-- The actual original inverse maps the complete weak class back to the original left model. -/
theorem toLeft_allWeakMaps : (weakEquivalences Spectrum.{u, v}) ≤
  ((weakEquivalences Spectrum.{u, v})).inverseImage
  (carrierEquivalence.{u, v}).inverse := by
  intro X Y f hf
  exact (toLeft_weakEquivalences_iff f).mpr hf

/-- The whole original forward left-derived comparison is invertible on all objects. -/
theorem toRightDerived_leftComparison_isIso : IsIso (toRightDerivedAdjunctionData.{u,
  v}).leftComparison :=
  quillenDerived_leftComparison_isIso
    (carrierEquivalence.{u, v}).toAdjunction
    toRight_allWeakMaps

/-- The original forward right-derived comparison is an isomorphism of entire functors. -/
theorem toRightDerived_rightComparison_isIso : IsIso (toRightDerivedAdjunctionData.{u,
  v}).rightComparison :=
  quillenDerived_rightComparison_isIso
    (carrierEquivalence.{u, v}).toAdjunction
    toLeft_allWeakMaps

/-- The actual inverse left comparison is invertible on every original right object. -/
theorem toLeftDerived_leftComparison_isIso : IsIso (toLeftDerivedAdjunctionData.{u,
  v}).leftComparison :=
  quillenDerived_leftComparison_isIso
    (carrierEquivalence.{u, v}).symm.toAdjunction
    toLeft_allWeakMaps

/-- The actual inverse right comparison retains the entire original forward functor. -/
theorem toLeftDerived_rightComparison_isIso : IsIso (toLeftDerivedAdjunctionData.{u,
  v}).rightComparison :=
  quillenDerived_rightComparison_isIso
    (carrierEquivalence.{u, v}).symm.toAdjunction
    toRight_allWeakMaps

/-- The exact original forward left comparison, as a whole natural isomorphism. -/
def toRightDerivedLeftComparisonIso :
    ((weakEquivalences Spectrum.{u, v})).Q ⋙
      (toRightDerivedAdjunctionData.{u, v}).leftDerived ≅
      (carrierEquivalence.{u, v}).functor ⋙
      ((weakEquivalences Spectrum.{u, v})).Q := by
  let _ : IsIso (toRightDerivedAdjunctionData.{u, v}).leftComparison :=
    toRightDerived_leftComparison_isIso
  exact asIso (toRightDerivedAdjunctionData.{u, v}).leftComparison

/-- The entire given forward right comparison, with its original map. -/
def toRightDerivedRightComparisonIso :
    (carrierEquivalence.{u, v}).inverse ⋙ ((weakEquivalences
      Spectrum.{u, v})).Q ≅ ((weakEquivalences
      Spectrum.{u, v})).Q ⋙ (toRightDerivedAdjunctionData.{u,
      v}).rightDerived := by
  let _ : IsIso (toRightDerivedAdjunctionData.{u, v}).rightComparison :=
    toRightDerived_rightComparison_isIso
  exact asIso (toRightDerivedAdjunctionData.{u, v}).rightComparison

/-- The whole original inverse left comparison is the same given natural transformation. -/
def toLeftDerivedLeftComparisonIso :
    ((weakEquivalences Spectrum.{u, v})).Q ⋙
      (toLeftDerivedAdjunctionData.{u, v}).leftDerived ≅
      (carrierEquivalence.{u, v}).inverse ⋙
      ((weakEquivalences Spectrum.{u, v})).Q := by
  let _ : IsIso (toLeftDerivedAdjunctionData.{u, v}).leftComparison :=
    toLeftDerived_leftComparison_isIso
  exact asIso (toLeftDerivedAdjunctionData.{u, v}).leftComparison

/-- The full inverse right comparison keeps the original forward conversion. -/
def toLeftDerivedRightComparisonIso :
    (carrierEquivalence.{u, v}).functor ⋙ ((weakEquivalences
      Spectrum.{u, v})).Q ≅ ((weakEquivalences
      Spectrum.{u, v})).Q ⋙ (toLeftDerivedAdjunctionData.{u, v}).rightDerived
      := by
  let _ : IsIso (toLeftDerivedAdjunctionData.{u, v}).rightComparison :=
    toLeftDerived_rightComparison_isIso
  exact asIso (toLeftDerivedAdjunctionData.{u, v}).rightComparison

/-- The first whole forward comparison uses exactly the original derived counit map. -/
theorem toRightDerivedLeftComparisonIso_hom :
    toRightDerivedLeftComparisonIso.{u, v}.hom = (toRightDerivedAdjunctionData.{u,
      v}).leftComparison := rfl

/-- The other whole forward comparison keeps exactly the original derived unit map. -/
theorem toRightDerivedRightComparisonIso_hom :
    toRightDerivedRightComparisonIso.{u, v}.hom = (toRightDerivedAdjunctionData.{u,
      v}).rightComparison := rfl

/-- The whole inverse left comparison retains the complete given original map. -/
theorem toLeftDerivedLeftComparisonIso_hom :
    toLeftDerivedLeftComparisonIso.{u, v}.hom = (toLeftDerivedAdjunctionData.{u,
      v}).leftComparison := rfl

/-- The whole inverse right comparison keeps the complete original forward map. -/
theorem toLeftDerivedRightComparisonIso_hom :
    toLeftDerivedRightComparisonIso.{u, v}.hom = (toLeftDerivedAdjunctionData.{u,
      v}).rightComparison := rfl

/-- The original forward canonical derived adjunction, as an equivalence of its localizations. -/
def toRightCanonicalDerivedEquivalence : ((weakEquivalences Spectrum.{u, v})).Localization ≌ ((weakEquivalences
  Spectrum.{u, v})).Localization :=
  homotopicalQuillenDerivedEquivalence
    (carrierEquivalence.{u, v}).toAdjunction
    toRight_allWeakMaps toLeft_allWeakMaps

/-- The original inverse canonical derived adjunction, retaining its two given total functors. -/
def toLeftCanonicalDerivedEquivalence : ((weakEquivalences Spectrum.{u, v})).Localization ≌ ((weakEquivalences
  Spectrum.{u, v})).Localization :=
  homotopicalQuillenDerivedEquivalence
    (carrierEquivalence.{u, v}).symm.toAdjunction
    toLeft_allWeakMaps toRight_allWeakMaps

/-- The complete forward equivalence functor is the actual original total left derived value. -/
theorem toRightCanonicalDerivedEquivalence_functor :
    toRightCanonicalDerivedEquivalence.{u, v}.functor = (toRightDerivedAdjunctionData.{u,
      v}).leftDerived := rfl

/-- Its whole inverse is the original canonical total right derived value. -/
theorem toRightCanonicalDerivedEquivalence_inverse :
    toRightCanonicalDerivedEquivalence.{u, v}.inverse = (toRightDerivedAdjunctionData.{u,
      v}).rightDerived := rfl

/-- The original forward unit is unchanged as a full natural transformation. -/
theorem toRightCanonicalDerivedEquivalence_unit_hom :
    toRightCanonicalDerivedEquivalence.{u, v}.unitIso.hom = (toRightDerivedAdjunctionData.{u,
      v}).adjunction.unit := rfl

/-- The entire forward counit is the actual original derived-adjunction counit. -/
theorem toRightCanonicalDerivedEquivalence_counit_hom :
    toRightCanonicalDerivedEquivalence.{u, v}.counitIso.hom = (toRightDerivedAdjunctionData.{u,
      v}).adjunction.counit := rfl

/-- The entire inverse equivalence functor keeps the original inverse left-derived choice. -/
theorem toLeftCanonicalDerivedEquivalence_functor :
    toLeftCanonicalDerivedEquivalence.{u, v}.functor = (toLeftDerivedAdjunctionData.{u,
      v}).leftDerived := rfl

/-- Its full inverse is the given original inverse right-derived choice. -/
theorem toLeftCanonicalDerivedEquivalence_inverse :
    toLeftCanonicalDerivedEquivalence.{u, v}.inverse = (toLeftDerivedAdjunctionData.{u,
      v}).rightDerived := rfl

/-- The original inverse derived unit is the same complete natural transformation. -/
theorem toLeftCanonicalDerivedEquivalence_unit_hom :
    toLeftCanonicalDerivedEquivalence.{u, v}.unitIso.hom = (toLeftDerivedAdjunctionData.{u,
      v}).adjunction.unit := rfl

/-- The original inverse derived counit remains the actual given complete map. -/
theorem toLeftCanonicalDerivedEquivalence_counit_hom :
    toLeftCanonicalDerivedEquivalence.{u, v}.counitIso.hom = (toLeftDerivedAdjunctionData.{u,
      v}).adjunction.counit := rfl

/-- The whole forward unit retains its original conversion-unit factorization. -/
theorem toRightCanonicalDerivedEquivalence_unit_fac (X : Spectrum.{u, v}) :
    toRightCanonicalDerivedEquivalence.unitIso.hom.app (((weakEquivalences
      Spectrum.{u, v})).Q.obj X) ≫
        (toRightDerivedAdjunctionData.{u, v}).rightDerived.map ((toRightDerivedAdjunctionData.{u,
          v}).leftComparison.app X) =
      ((weakEquivalences Spectrum.{u, v})).Q.map
        ((carrierEquivalence.{u, v}).unitIso.hom.app X) ≫
        (toRightDerivedAdjunctionData.{u, v}).rightComparison.app
        ((carrierEquivalence.{u, v}).functor.obj X) :=
  quillenDerived_unit_fac (carrierEquivalence.{u, v}).toAdjunction X

/-- The actual entire forward counit keeps the original conversion-counit factorization. -/
theorem toRightCanonicalDerivedEquivalence_counit_fac (Y : Spectrum.{u, v}) :
    (toRightDerivedAdjunctionData.{u, v}).leftDerived.map ((toRightDerivedAdjunctionData.{u,
      v}).rightComparison.app Y) ≫
        toRightCanonicalDerivedEquivalence.counitIso.hom.app (((weakEquivalences
          Spectrum.{u, v})).Q.obj Y) =
      (toRightDerivedAdjunctionData.{u, v}).leftComparison.app
        ((carrierEquivalence.{u, v}).inverse.obj Y) ≫
        ((weakEquivalences Spectrum.{u, v})).Q.map
        ((carrierEquivalence.{u, v}).counitIso.hom.app Y) :=
  quillenDerived_counit_fac (carrierEquivalence.{u, v}).toAdjunction Y

/-- The whole inverse unit retains the same actual inverse-conversion unit. -/
theorem toLeftCanonicalDerivedEquivalence_unit_fac (Y : Spectrum.{u, v}) :
    toLeftCanonicalDerivedEquivalence.unitIso.hom.app (((weakEquivalences
      Spectrum.{u, v})).Q.obj Y) ≫
        (toLeftDerivedAdjunctionData.{u, v}).rightDerived.map ((toLeftDerivedAdjunctionData.{u,
          v}).leftComparison.app Y) =
      ((weakEquivalences Spectrum.{u, v})).Q.map
        ((carrierEquivalence.{u, v}).symm.unitIso.hom.app Y)
        ≫
        (toLeftDerivedAdjunctionData.{u, v}).rightComparison.app
          ((carrierEquivalence.{u, v}).inverse.obj Y) :=
  quillenDerived_unit_fac (carrierEquivalence.{u, v}).symm.toAdjunction Y

/-- The actual inverse counit has the original full inverse-conversion counit equation. -/
theorem toLeftCanonicalDerivedEquivalence_counit_fac (X : Spectrum.{u, v}) :
    (toLeftDerivedAdjunctionData.{u, v}).leftDerived.map ((toLeftDerivedAdjunctionData.{u,
      v}).rightComparison.app X) ≫
        toLeftCanonicalDerivedEquivalence.counitIso.hom.app (((weakEquivalences
          Spectrum.{u, v})).Q.obj X) =
      (toLeftDerivedAdjunctionData.{u, v}).leftComparison.app
        ((carrierEquivalence.{u, v}).functor.obj X) ≫
        ((weakEquivalences Spectrum.{u, v})).Q.map
          ((carrierEquivalence.{u, v}).symm.counitIso.hom.app X) :=
  quillenDerived_counit_fac (carrierEquivalence.{u, v}).symm.toAdjunction X

/-- Every original left map retains the full canonical forward left-comparison square. -/
theorem toRightDerived_leftComparison_naturality
    {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    (toRightDerivedAdjunctionData.{u, v}).leftDerived.map (((weakEquivalences
      Spectrum.{u, v})).Q.map f) ≫ (toRightDerivedAdjunctionData.{u,
      v}).leftComparison.app Y =
      (toRightDerivedAdjunctionData.{u, v}).leftComparison.app X ≫ ((weakEquivalences
        Spectrum.{u, v})).Q.map
        ((carrierEquivalence.{u, v}).functor.map f) :=
  (toRightDerivedAdjunctionData.{u, v}).leftComparison.naturality f

/-- Every original right map keeps the entire original forward right-comparison square. -/
theorem toRightDerived_rightComparison_naturality
    {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    ((weakEquivalences Spectrum.{u, v})).Q.map
      ((carrierEquivalence.{u, v}).inverse.map f) ≫
      (toRightDerivedAdjunctionData.{u, v}).rightComparison.app Y =
      (toRightDerivedAdjunctionData.{u, v}).rightComparison.app X ≫
        (toRightDerivedAdjunctionData.{u, v}).rightDerived.map (((weakEquivalences
        Spectrum.{u, v})).Q.map f) :=
  (toRightDerivedAdjunctionData.{u, v}).rightComparison.naturality f

/-- The original inverse left comparison is natural on whole right-module arrows. -/
theorem toLeftDerived_leftComparison_naturality
    {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    (toLeftDerivedAdjunctionData.{u, v}).leftDerived.map (((weakEquivalences
      Spectrum.{u, v})).Q.map f) ≫ (toLeftDerivedAdjunctionData.{u,
      v}).leftComparison.app Y =
      (toLeftDerivedAdjunctionData.{u, v}).leftComparison.app X ≫ ((weakEquivalences
        Spectrum.{u, v})).Q.map
        ((carrierEquivalence.{u, v}).inverse.map f) :=
  (toLeftDerivedAdjunctionData.{u, v}).leftComparison.naturality f

/-- The entire inverse right comparison keeps every given original left-module arrow. -/
theorem toLeftDerived_rightComparison_naturality
    {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    ((weakEquivalences Spectrum.{u, v})).Q.map
      ((carrierEquivalence.{u, v}).functor.map f) ≫
      (toLeftDerivedAdjunctionData.{u, v}).rightComparison.app Y =
      (toLeftDerivedAdjunctionData.{u, v}).rightComparison.app X ≫
        (toLeftDerivedAdjunctionData.{u, v}).rightDerived.map (((weakEquivalences
        Spectrum.{u, v})).Q.map f) :=
  (toLeftDerivedAdjunctionData.{u, v}).rightComparison.naturality f

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel.Canonical
