/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalApplication.StrictSourceComparison

/-!
# Actual original literal strict D_R factor classes and original replacements

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

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalStrictReplacement

attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The original strict I first factor has the actual supplied strict initial object. -/
abbrev initialToCofibrantReplacement :
    (Functor.const StrictSourceCarrier.{u, v}).obj zero ⟶ cofibrantReplacement :=
  Functor.whiskerLeft fromZeroArrow strictOriginalCofibrantFactorizationData.i

/-- The original strict J second factor has the same actual supplied strict terminal object. -/
abbrev fibrantReplacementToZero :
    fibrantReplacement.{u, v} ⟶ (Functor.const StrictSourceCarrier.{u, v}).obj zero :=
  Functor.whiskerLeft toZeroArrow strictOriginalFibrantFactorizationData.p

/-- The entire original Q initial Arrow factorization retains its exact actual source classes. -/
theorem cofibrantFactor_classes (X : StrictSourceCarrier.{u, v}) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    cofibrations StrictSourceCarrier.{u, v} (strictOriginalCofibrantFactorizationData.i.app
      (fromZeroArrow.obj X)) ∧
      trivialFibrations StrictSourceCarrier.{u, v}
        (strictOriginalCofibrantFactorizationData.p.app (fromZeroArrow.obj X)) :=
  strictOriginalCofibrantFactorizationData_classes (fromZeroArrow.obj X)

/-- The entire original R terminal Arrow factorization retains its exact actual source classes. -/
theorem fibrantFactor_classes (X : StrictSourceCarrier.{u, v}) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} :=
      EnrichedProjective.BasedNativePresentation.strictModelCategory
    trivialCofibrations StrictSourceCarrier.{u, v} (strictOriginalFibrantFactorizationData.i.app
      (toZeroArrow.obj X)) ∧
      fibrations StrictSourceCarrier.{u, v} (strictOriginalFibrantFactorizationData.p.app
        (toZeroArrow.obj X)) :=
  strictOriginalFibrantFactorizationData_classes (toZeroArrow.obj X)

/-- The original source π is weak in the actual returned source model. -/
theorem cofibrantProjection_weak (X : StrictSourceCarrier.{u, v}) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} := BasedNativePresentation.strictModelCategory
    weakEquivalences StrictSourceCarrier (cofibrantProjection.app X) :=
  (strictOriginalCofibrantFactorizationData_classes (fromZeroArrow.obj X)).2.2

/-- The original source ι is weak in the actual returned source model. -/
theorem fibrantUnit_weak (X : StrictSourceCarrier.{u, v}) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} := BasedNativePresentation.strictModelCategory
    weakEquivalences StrictSourceCarrier (fibrantUnit.app X) :=
  (strictOriginalFibrantFactorizationData_classes (toZeroArrow.obj X)).1.2

omit B in
/-- The complete original source π square retains every original source morphism. -/
theorem cofibrantProjection_naturality [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {X Y :
  StrictSourceCarrier.{u, v}} (f : X ⟶ Y) :
    cofibrantReplacement.map f ≫ cofibrantProjection.app Y =
    cofibrantProjection.app X ≫ (𝟭 StrictSourceCarrier.{u, v}).map f :=
  cofibrantProjection.naturality f

omit B in
/-- The complete original source ι square retains every original source morphism. -/
theorem fibrantUnit_naturality [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {X Y : StrictSourceCarrier.{u,
  v}} (f : X ⟶ Y) :
    (𝟭 StrictSourceCarrier.{u, v}).map f ≫ fibrantUnit.app Y =
    fibrantUnit.app X ≫ fibrantReplacement.map f :=
  fibrantUnit.naturality f

/-- Both I/J original data factor the complete original source initial Arrow. -/
theorem cofibrant_fac (X : StrictSourceCarrier.{u, v}) :
    strictOriginalCofibrantFactorizationData.i.app (fromZeroArrow.obj X) ≫
    strictOriginalCofibrantFactorizationData.p.app (fromZeroArrow.obj X) = (fromZeroArrow.obj
      X).hom :=
  strictOriginalCofibrantFactorizationData_fac (fromZeroArrow.obj X)

/-- Both I/J original data factor the complete original source terminal Arrow. -/
theorem fibrant_fac (X : StrictSourceCarrier.{u, v}) :
    strictOriginalFibrantFactorizationData.i.app (toZeroArrow.obj X) ≫
    strictOriginalFibrantFactorizationData.p.app (toZeroArrow.obj X) = (toZeroArrow.obj X).hom :=
  strictOriginalFibrantFactorizationData_fac (toZeroArrow.obj X)

/-- The actual original Q middle is cofibrant through its same I first-factor zero map. -/
theorem isCofibrant_cofibrantReplacement (X : StrictSourceCarrier.{u, v}) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} := BasedNativePresentation.strictModelCategory
    IsCofibrant (cofibrantReplacement.obj X) := by
  let _ : ModelCategory StrictSourceCarrier.{u, v} := BasedNativePresentation.strictModelCategory
  exact (isCofibrant_iff_of_isInitial (initialToCofibrantReplacement.app X)
    zero_isZero.isInitial).mpr
      ((HomotopicalAlgebra.cofibration_iff _).mpr (strictOriginalCofibrantFactorizationData_classes
        (fromZeroArrow.obj X)).1)

/-- The actual original R middle is fibrant through its same J second-factor zero map. -/
theorem isFibrant_fibrantReplacement (X : StrictSourceCarrier.{u, v}) :
    let _ : ModelCategory StrictSourceCarrier.{u, v} := BasedNativePresentation.strictModelCategory
    IsFibrant (fibrantReplacement.obj X) := by
  let _ : ModelCategory StrictSourceCarrier.{u, v} := BasedNativePresentation.strictModelCategory
  exact (isFibrant_iff_of_isTerminal (fibrantReplacementToZero.app X)
    zero_isZero.isTerminal).mpr
      ((HomotopicalAlgebra.fibration_iff _).mpr (strictOriginalFibrantFactorizationData_classes
        (toZeroArrow.obj X)).2)

omit B in
/-- The actual original zero maps to a genuine canonical zero through the full equivalence. -/
theorem canonical_zero_isZero : IsZero (canonicalStrictSourcePresentation.functor.obj zero.{u, v}) :=
  IsZero.of_full_of_faithful_of_isZero canonicalStrictSourcePresentation.inverse
    (canonicalStrictSourcePresentation.functor.obj zero)
      (zero_isZero.of_iso (canonicalStrictSourcePresentation.unitIso.app zero).symm)


/-- The same original I first map proves cofibrancy of its actual canonical image. -/
theorem isCofibrant_nativeCofibrantReplacement (X : StrictSourceCarrier.{u, v}) :
    IsCofibrant (canonicalStrictSourcePresentation.functor.obj (cofibrantReplacement.obj X)) := by
  apply (isCofibrant_iff_of_isInitial
    (canonicalStrictSourcePresentation.functor.map (initialToCofibrantReplacement.app X))
      canonical_zero_isZero.isInitial).mpr
  exact (HomotopicalAlgebra.cofibration_iff _).mpr
    (strictOriginalCofibrantFactorizationData_canonical_classes (fromZeroArrow.obj X)).1

/-- The same original J second map proves fibrancy of its actual canonical image. -/
theorem isFibrant_nativeFibrantReplacement (X : StrictSourceCarrier.{u, v}) :
    IsFibrant (canonicalStrictSourcePresentation.functor.obj (fibrantReplacement.obj X)) := by
  apply (isFibrant_iff_of_isTerminal
    (canonicalStrictSourcePresentation.functor.map (fibrantReplacementToZero.app X))
      canonical_zero_isZero.isTerminal).mpr
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (strictOriginalFibrantFactorizationData_canonical_classes (toZeroArrow.obj X)).2


end PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalStrictReplacement
