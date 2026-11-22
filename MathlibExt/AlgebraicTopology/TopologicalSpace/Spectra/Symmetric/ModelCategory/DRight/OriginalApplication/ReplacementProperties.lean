/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalApplication.Replacement

/-!
# Actual original D_R replacement factor classes and source weak preservation

The original OLD-J source data give actual C/TF and TC/F factor maps.
Their original π/ι naturality detects weak maps through the same returned
source model, with no replacement or localization dictionary as an input.
The original map and factor statements retain `_B` to quantify over every caller
bottom of the given κ algorithm. The canonical implementation uses the
unique original bottom, and the whole-record readbacks identify it at every `_B`.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory MonoidalClosed ZeroObject

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalReplacement

attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The entire original Q initial Arrow factorization retains its exact actual source classes. -/
theorem cofibrantFactor_classes (X : SourceCarrier.{u, v}) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    cofibrations SourceCarrier.{u, v} (originalCofibrantFactorizationData.i.app
      (fromZeroArrow.obj X)) ∧
      trivialFibrations SourceCarrier.{u, v} (originalCofibrantFactorizationData.p.app
        (fromZeroArrow.obj X)) :=
  originalCofibrantFactorizationData_classes (fromZeroArrow.obj X)

/-- The entire original R terminal Arrow factorization retains its exact actual source classes. -/
theorem fibrantFactor_classes (X : SourceCarrier.{u, v}) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    trivialCofibrations SourceCarrier.{u, v} (originalFibrantFactorizationData.i.app
      (toZeroArrow.obj X)) ∧
      fibrations SourceCarrier.{u, v} (originalFibrantFactorizationData.p.app (toZeroArrow.obj
        X)) :=
  originalFibrantFactorizationData_classes (toZeroArrow.obj X)

/-- The original source π is weak in the actual returned source model. -/
theorem cofibrantProjection_weak (X : SourceCarrier.{u, v}) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    weakEquivalences SourceCarrier (cofibrantProjection.app X) :=
  (originalCofibrantFactorizationData_classes (fromZeroArrow.obj X)).2.2

/-- The original source ι is weak in the actual returned source model. -/
theorem fibrantUnit_weak (X : SourceCarrier.{u, v}) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    weakEquivalences SourceCarrier (fibrantUnit.app X) :=
  (originalFibrantFactorizationData_classes (toZeroArrow.obj X)).1.2

omit B in
/-- The complete original source π square retains every original source morphism. -/
theorem cofibrantProjection_naturality [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {X Y : SourceCarrier.{u,
  v}} (f : X ⟶ Y) :
    cofibrantReplacement.map f ≫ cofibrantProjection.app Y =
    cofibrantProjection.app X ≫ (𝟭 SourceCarrier.{u, v}).map f :=
  cofibrantProjection.naturality f

omit B in
/-- The complete original source ι square retains every original source morphism. -/
theorem fibrantUnit_naturality [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {X Y : SourceCarrier.{u, v}} (f
  : X ⟶ Y) :
    (𝟭 SourceCarrier.{u, v}).map f ≫ fibrantUnit.app Y =
    fibrantUnit.app X ≫ fibrantReplacement.map f :=
  fibrantUnit.naturality f

/-- Both I/J original data factor the complete original source initial Arrow. -/
theorem cofibrant_fac (X : SourceCarrier.{u, v}) :
    originalCofibrantFactorizationData.i.app (fromZeroArrow.obj X) ≫
    originalCofibrantFactorizationData.p.app (fromZeroArrow.obj X) = (fromZeroArrow.obj X).hom :=
  originalCofibrantFactorizationData_fac (fromZeroArrow.obj X)

/-- Both I/J original data factor the complete original source terminal Arrow. -/
theorem fibrant_fac (X : SourceCarrier.{u, v}) :
    originalFibrantFactorizationData.i.app (toZeroArrow.obj X) ≫
    originalFibrantFactorizationData.p.app (toZeroArrow.obj X) = (toZeroArrow.obj X).hom :=
  originalFibrantFactorizationData_fac (toZeroArrow.obj X)

/-- The actual original Q middle is cofibrant through its same I first-factor zero map. -/
theorem isCofibrant_cofibrantReplacement (X : SourceCarrier.{u, v}) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    IsCofibrant (cofibrantReplacement.obj X) := by
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  exact (isCofibrant_iff_of_isInitial (initialToCofibrantReplacement.app X)
    zero_isZero.isInitial).mpr
      ((HomotopicalAlgebra.cofibration_iff _).mpr (originalCofibrantFactorizationData_classes
        (fromZeroArrow.obj X)).1)

/-- The actual original R middle is fibrant through its same J second-factor zero map. -/
theorem isFibrant_fibrantReplacement (X : SourceCarrier.{u, v}) :
    let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
      PointedCGWH.SymmetricDRight.Index))
    IsFibrant (fibrantReplacement.obj X) := by
  let _ : ModelCategory SourceCarrier.{u, v} := (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A :=
    PointedCGWH.SymmetricDRight.Index))
  exact (isFibrant_iff_of_isTerminal (fibrantReplacementToZero.app X)
    zero_isZero.isTerminal).mpr
      ((HomotopicalAlgebra.fibration_iff _).mpr (originalFibrantFactorizationData_classes
        (toZeroArrow.obj X)).2)

omit B in
/-- The actual original zero maps to a genuine canonical zero through the full equivalence. -/
theorem canonical_zero_isZero : IsZero (canonicalSourcePresentation.functor.obj zero.{u, v}) :=
  IsZero.of_full_of_faithful_of_isZero canonicalSourcePresentation.inverse
    (canonicalSourcePresentation.functor.obj zero)
      (zero_isZero.of_iso (canonicalSourcePresentation.unitIso.app zero).symm)


/-- The same original I first map proves cofibrancy of its actual canonical image. -/
theorem isCofibrant_nativeCofibrantReplacement (X : SourceCarrier.{u, v}) :
    IsCofibrant (canonicalSourcePresentation.functor.obj (cofibrantReplacement.obj X)) := by
  apply (isCofibrant_iff_of_isInitial
    (canonicalSourcePresentation.functor.map (initialToCofibrantReplacement.app X))
      canonical_zero_isZero.isInitial).mpr
  exact (HomotopicalAlgebra.cofibration_iff _).mpr
    (originalCofibrantFactorizationData_canonical_classes (fromZeroArrow.obj X)).1

/-- The same original J second map proves fibrancy of its actual canonical image. -/
theorem isFibrant_nativeFibrantReplacement (X : SourceCarrier.{u, v}) :
    IsFibrant (canonicalSourcePresentation.functor.obj (fibrantReplacement.obj X)) := by
  apply (isFibrant_iff_of_isTerminal
    (canonicalSourcePresentation.functor.map (fibrantReplacementToZero.app X))
      canonical_zero_isZero.isTerminal).mpr
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (originalFibrantFactorizationData_canonical_classes (toZeroArrow.obj X)).2


end PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalReplacement
