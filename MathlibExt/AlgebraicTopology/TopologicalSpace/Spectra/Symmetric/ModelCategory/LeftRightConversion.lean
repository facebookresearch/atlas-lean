/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.LeftPresentationModel
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.RightModules
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.CanonicalProjectiveModels

/-!
# Native projective models on the original left and right sphere modules

The original sphere-module conversion preserves the full underlying sequence and every original
level map. It therefore identifies the five classes of the two actual native projective models.
The two original conversion adjunctions are Quillen equivalences for those same model values.
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

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- Every original left sphere-module level object is kept by the complete conversion. -/
theorem toRight_levelObj (M : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (n : I) :
    ((SymmetricRightModulePresentation.sphereModuleEquivalence.functor.obj M).X.functor.obj n) =
      M.X.functor.obj n := rfl

/-- The actual original inverse retains every full right sphere-module level object. -/
theorem toLeft_levelObj (M : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) (n : I) :
    ((SymmetricRightModulePresentation.sphereModuleEquivalence.inverse.obj M).X.functor.obj n) =
      M.X.functor.obj n := rfl

/-- The original conversion keeps every full left-module level arrow. -/
theorem toRight_levelMap {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) (n : I) :
    (SymmetricRightModulePresentation.sphereModuleEquivalence.functor.map f).hom.natTrans.app n =
      f.hom.natTrans.app n := by
  change (CommutativeModuleConversion.toRightMap sphereSequence.{u, v} f).hom.natTrans.app n = _
  rw [CommutativeModuleConversion.toRightMap_hom]

/-- The actual inverse conversion keeps every full original right-module level arrow. -/
theorem toLeft_levelMap {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : M ⟶ N) (n :
  I) :
    (SymmetricRightModulePresentation.sphereModuleEquivalence.inverse.map f).hom.natTrans.app n =
      f.hom.natTrans.app n := by
  change (CommutativeModuleConversion.toLeftMap sphereSequence.{u, v} f).hom.natTrans.app n = _
  rw [CommutativeModuleConversion.toLeftMap_hom]

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

/-- The actual original conversion identifies weak equivalences at every original level. -/
theorem toRight_weakEquivalences_iff {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.functor.map f) ↔
      weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f := by
  constructor
  · intro h
    apply (LeftPresentationModel.weakEquivalences_iff f).mpr
    intro n
    simpa only [toRight_levelMap, toRight_levelObj] using
      ((RightPresentationModel.weakEquivalences_iff _).mp h n)
  · intro h
    apply (RightPresentationModel.weakEquivalences_iff _).mpr
    intro n
    simpa only [toRight_levelMap, toRight_levelObj] using
      ((LeftPresentationModel.weakEquivalences_iff f).mp h n)

/-- The actual original inverse identifies weak equivalences on the full right-module arrows. -/
theorem toLeft_weakEquivalences_iff {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : M
  ⟶ N) :
    weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.inverse.map f) ↔
      weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} f := by
  constructor
  · intro h
    apply (RightPresentationModel.weakEquivalences_iff f).mpr
    intro n
    simpa only [toLeft_levelMap, toLeft_levelObj] using
      ((LeftPresentationModel.weakEquivalences_iff _).mp h n)
  · intro h
    apply (LeftPresentationModel.weakEquivalences_iff _).mpr
    intro n
    simpa only [toLeft_levelMap, toLeft_levelObj] using
      ((RightPresentationModel.weakEquivalences_iff f).mp h n)

/-- Fibrations are preserved and reflected by the unchanged original conversion. -/
theorem toRight_fibrations_iff {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    fibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.functor.map f) ↔
      fibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f := by
  constructor
  · intro h
    apply (LeftPresentationModel.fibrations_iff f).mpr
    intro n
    simpa only [toRight_levelMap, toRight_levelObj] using
      ((RightPresentationModel.fibrations_iff _).mp h n)
  · intro h
    apply (RightPresentationModel.fibrations_iff _).mpr
    intro n
    simpa only [toRight_levelMap, toRight_levelObj] using
      ((LeftPresentationModel.fibrations_iff f).mp h n)

/-- The whole inverse conversion preserves and reflects original right fibrations. -/
theorem toLeft_fibrations_iff {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : M ⟶ N)
  :
    fibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.inverse.map f) ↔
      fibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} f := by
  constructor
  · intro h
    apply (RightPresentationModel.fibrations_iff f).mpr
    intro n
    simpa only [toLeft_levelMap, toLeft_levelObj] using
      ((LeftPresentationModel.fibrations_iff _).mp h n)
  · intro h
    apply (LeftPresentationModel.fibrations_iff _).mpr
    intro n
    simpa only [toLeft_levelMap, toLeft_levelObj] using
      ((RightPresentationModel.fibrations_iff f).mp h n)

/-- The actual original conversion identifies the full trivial-fibration class. -/
theorem toRight_trivialFibrations_iff {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    trivialFibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.functor.map f) ↔
      trivialFibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f := by
  constructor
  · intro h
    apply (LeftPresentationModel.trivialFibrations_iff f).mpr
    intro n
    simpa only [toRight_levelMap, toRight_levelObj] using
      ((RightPresentationModel.trivialFibrations_iff _).mp h n)
  · intro h
    apply (RightPresentationModel.trivialFibrations_iff _).mpr
    intro n
    simpa only [toRight_levelMap, toRight_levelObj] using
      ((LeftPresentationModel.trivialFibrations_iff f).mp h n)

/-- The full inverse conversion preserves and reflects the original trivial-fibration class. -/
theorem toLeft_trivialFibrations_iff {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f :
  M ⟶ N) :
    trivialFibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.inverse.map f) ↔
      trivialFibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} f := by
  constructor
  · intro h
    apply (RightPresentationModel.trivialFibrations_iff f).mpr
    intro n
    simpa only [toLeft_levelMap, toLeft_levelObj] using
      ((LeftPresentationModel.trivialFibrations_iff _).mp h n)
  · intro h
    apply (LeftPresentationModel.trivialFibrations_iff _).mpr
    intro n
    simpa only [toLeft_levelMap, toLeft_levelObj] using
      ((RightPresentationModel.trivialFibrations_iff f).mp h n)

/-- The genuine sphere-module forward adjunction is Quillen for the two actual native models. -/
theorem toRight_isQuillenAdjunction :
    Adjunction.IsQuillenAdjunction
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.toAdjunction) :=
  Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (fun _ _ f hf => (toLeft_fibrations_iff f).mpr hf)
    (fun _ _ f hf => (toLeft_trivialFibrations_iff f).mpr hf)

/-- The actual original inverse adjunction is Quillen for the same two native model values. -/
theorem toLeft_isQuillenAdjunction :
    Adjunction.IsQuillenAdjunction
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm.toAdjunction) :=
  Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (fun _ _ f hf => (toRight_fibrations_iff f).mpr hf)
    (fun _ _ f hf => (toRight_trivialFibrations_iff f).mpr hf)

/-- The whole conversion preserves and reflects the original native cofibration class. -/
theorem toRight_cofibrations_iff {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    cofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.functor.map f) ↔
      cofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f := by
  let E := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
  let _ : E.toAdjunction.IsQuillenAdjunction := toRight_isQuillenAdjunction
  let _ : E.symm.toAdjunction.IsQuillenAdjunction := toLeft_isQuillenAdjunction
  constructor
  · intro h
    have hBack :=
      (inferInstance : E.symm.toAdjunction.IsQuillenAdjunction).preservesCofibrations _ h
    exact ((cofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).arrow_mk_iso_iff
      (Arrow.isoOfNatIso E.unitIso (Arrow.mk f))).mpr hBack
  · intro h
    exact (inferInstance : E.toAdjunction.IsQuillenAdjunction).preservesCofibrations _ h

/-- The genuine original inverse also identifies the full native cofibration class. -/
theorem toLeft_cofibrations_iff {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : M ⟶
  N) :
    cofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.inverse.map f) ↔
      cofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} f := by
  let E := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
  let _ : E.toAdjunction.IsQuillenAdjunction := toRight_isQuillenAdjunction
  let _ : E.symm.toAdjunction.IsQuillenAdjunction := toLeft_isQuillenAdjunction
  constructor
  · intro h
    have hBack := (inferInstance : E.toAdjunction.IsQuillenAdjunction).preservesCofibrations _ h
    exact ((cofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).arrow_mk_iso_iff
      (Arrow.isoOfNatIso E.counitIso (Arrow.mk f))).mp hBack
  · intro h
    exact (inferInstance : E.symm.toAdjunction.IsQuillenAdjunction).preservesCofibrations _ h

/-- Every original trivial cofibration is preserved and reflected by the entire conversion. -/
theorem toRight_trivialCofibrations_iff {M N : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}} (f : M ⟶ N) :
    trivialCofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.functor.map f) ↔
      trivialCofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f := by
  let E := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
  let _ : E.toAdjunction.IsQuillenAdjunction := toRight_isQuillenAdjunction
  let _ : E.symm.toAdjunction.IsQuillenAdjunction := toLeft_isQuillenAdjunction
  constructor
  · intro h
    have hBack :=
      (inferInstance : E.symm.toAdjunction.IsQuillenAdjunction).preservesTrivialCofibrations _ h
    exact ((trivialCofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).arrow_mk_iso_iff
      (Arrow.isoOfNatIso E.unitIso (Arrow.mk f))).mpr hBack
  · intro h
    exact (inferInstance : E.toAdjunction.IsQuillenAdjunction).preservesTrivialCofibrations _ h

/-- The actual original inverse identifies the full native trivial-cofibration class. -/
theorem toLeft_trivialCofibrations_iff {M N : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f
  : M ⟶ N) :
    trivialCofibrations PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.inverse.map f) ↔
      trivialCofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} f := by
  let E := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
  let _ : E.toAdjunction.IsQuillenAdjunction := toRight_isQuillenAdjunction
  let _ : E.symm.toAdjunction.IsQuillenAdjunction := toLeft_isQuillenAdjunction
  constructor
  · intro h
    have hBack :=
      (inferInstance : E.toAdjunction.IsQuillenAdjunction).preservesTrivialCofibrations _ h
    exact ((trivialCofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).arrow_mk_iso_iff
      (Arrow.isoOfNatIso E.counitIso (Arrow.mk f))).mp hBack
  · intro h
    exact (inferInstance : E.symm.toAdjunction.IsQuillenAdjunction).preservesTrivialCofibrations _ h

/-- The full original forward adjunct preserves and reflects every weak equivalence. -/
theorem toRight_homEquiv_weakEquivalences_iff
    (M : PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}) (N :
      PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
    (f : SymmetricRightModulePresentation.sphereModuleEquivalence.functor.obj M ⟶ N) :
    weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} f ↔
      weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.toAdjunction.homEquiv M N f) := by
  let E := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
  rw [E.toAdjunction.homEquiv_unit]
  exact (toLeft_weakEquivalences_iff f).symm.trans
    ((weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v}).cancel_left_of_respectsIso
      (E.unitIso.hom.app M) (E.inverse.map f)).symm

/-- The actual original inverse adjunct identifies weak equivalences on complete left arrows. -/
theorem toLeft_homEquiv_weakEquivalences_iff
    (M : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) (N :
      PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v})
    (f : SymmetricRightModulePresentation.sphereModuleEquivalence.inverse.obj M ⟶ N) :
    weakEquivalences PointedCGWH.SymmetricFreeEvaluation.Carrier.{u, v} f ↔
      weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}
        (SymmetricRightModulePresentation.sphereModuleEquivalence.symm.toAdjunction.homEquiv
          M N f) := by
  let E := SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}
  rw [E.symm.toAdjunction.homEquiv_unit]
  exact (toRight_weakEquivalences_iff f).symm.trans
    ((weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}).cancel_left_of_respectsIso
      (E.symm.unitIso.hom.app M) (E.functor.map f)).symm

/-- The actual sphere-module conversion is a Quillen equivalence for the same native models. -/
theorem toRight_isQuillenEquivalence :
    Adjunction.IsQuillenEquivalence
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.toAdjunction) := by
  let _ : Adjunction.IsQuillenAdjunction
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.toAdjunction) :=
    toRight_isQuillenAdjunction
  exact { homEquiv_weakEquivalence_iff := fun f => toRight_homEquiv_weakEquivalences_iff _ _ f }

/-- The original inverse conversion is a Quillen equivalence for the unchanged native models. -/
theorem toLeft_isQuillenEquivalence :
    Adjunction.IsQuillenEquivalence
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm.toAdjunction) := by
  let _ : Adjunction.IsQuillenAdjunction
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.symm.toAdjunction) :=
    toLeft_isQuillenAdjunction
  exact { homEquiv_weakEquivalence_iff := fun f => toLeft_homEquiv_weakEquivalences_iff _ _ f }

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel

namespace PointedCGWH.Spectra.Symmetric.LeftRightNativeModel.Canonical

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction
  PointedCGWH.Spectra.Symmetric.levelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The original complete left/right conversion on the canonical spectrum carrier.
Its forward and inverse are the actual source conversion conjugated by the
two proved operator equivalences. -/
def carrierEquivalence : Spectrum.{u, v} ≌ Spectrum.{u, v} :=
  (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.symm.trans
    SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}).trans
      SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}

/-- The full forward functor still uses the original left reconstruction,
the original sphere conversion, and the original right operator action. -/
theorem carrierEquivalence_functor : carrierEquivalence.{u, v}.functor =
    (SymmetricModulePresentation.operatorToModule.{u, v} ⋙
      SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.functor) ⋙
        SymmetricRightModulePresentation.rightModuleToOperator.{u, v} := rfl

/-- The inverse retains the actual right reconstruction and original inverse
sphere conversion on every object and map. -/
theorem carrierEquivalence_inverse : carrierEquivalence.{u, v}.inverse =
    SymmetricRightModulePresentation.operatorToRightModule.{u, v} ⋙
      (SymmetricRightModulePresentation.sphereModuleEquivalence.{u, v}.inverse ⋙
        SymmetricModulePresentation.moduleToOperator.{u, v}) := rfl

/-- The forward comparison is the genuine original right-operator counit. -/
def forwardComparisonIso : carrierEquivalence.{u, v}.functor ≅ 𝟭 Spectrum.{u, v} :=
  SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.counitIso

/-- The inverse comparison uses the same complete right-operator counit. -/
def inverseComparisonIso : carrierEquivalence.{u, v}.inverse ≅ 𝟭 Spectrum.{u, v} :=
  SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.counitIso

/-- All original degree objects are retained by the actual conjugated conversion. -/
theorem toRight_levelObj (M : Spectrum.{u, v}) (n : I) :
    (carrierEquivalence.functor.obj M).toEnrichedFunctor.obj (symmetricOperatorObj n) =
      M.toEnrichedFunctor.obj (symmetricOperatorObj n) := rfl

/-- The full native transformation component remains the original degree map. -/
theorem toRight_levelMap {M N : Spectrum.{u, v}} (f : M ⟶ N) (n : I) :
    EnrichedFunctorCat.component (carrierEquivalence.functor.map f) (symmetricOperatorObj n) =
      EnrichedFunctorCat.component f (symmetricOperatorObj n) := by
  change EnrichedFunctorCat.component
    (SymmetricRightModulePresentation.rightModuleToOperator.map
      (SymmetricRightModulePresentation.operatorToRightModule.map f)) (symmetricOperatorObj n) = _
  rw [SymmetricRightModulePresentation.rightModuleToOperator_component]
  change (CommutativeModuleConversion.toRightMap sphereSequence.{u, v}
    (SymmetricModulePresentation.reconstructedModuleMap f)).hom.natTrans.app n = _
  rw [CommutativeModuleConversion.toRightMap_hom,
    SymmetricModulePresentation.reconstructedModuleMap_hom]
  exact symmetricSequenceRestriction_component f n

/-- The actual inverse keeps the entire original degree component too. -/
theorem toLeft_levelMap {M N : Spectrum.{u, v}} (f : M ⟶ N) (n : I) :
    EnrichedFunctorCat.component (carrierEquivalence.inverse.map f) (symmetricOperatorObj n) =
      EnrichedFunctorCat.component f (symmetricOperatorObj n) :=
  toRight_levelMap f n

/-- Forward conversion preserves and reflects the whole canonical weak class. -/
theorem toRight_weakEquivalences_iff {M N : Spectrum.{u, v}} (f : M ⟶ N) :
    weakEquivalences Spectrum.{u, v} (carrierEquivalence.functor.map f) ↔
      weakEquivalences Spectrum.{u, v} f :=
  (weakEquivalences Spectrum.{u, v}).arrow_mk_iso_iff
    (Arrow.isoOfNatIso forwardComparisonIso (Arrow.mk f))

/-- Inverse conversion preserves and reflects the whole canonical weak class. -/
theorem toLeft_weakEquivalences_iff {M N : Spectrum.{u, v}} (f : M ⟶ N) :
    weakEquivalences Spectrum.{u, v} (carrierEquivalence.inverse.map f) ↔
      weakEquivalences Spectrum.{u, v} f :=
  (weakEquivalences Spectrum.{u, v}).arrow_mk_iso_iff
    (Arrow.isoOfNatIso inverseComparisonIso (Arrow.mk f))

/-- The full canonical fibration class is retained by the original forward action. -/
theorem toRight_fibrations_iff {M N : Spectrum.{u, v}} (f : M ⟶ N) :
    fibrations Spectrum.{u, v} (carrierEquivalence.functor.map f) ↔
      fibrations Spectrum.{u, v} f :=
  (fibrations Spectrum.{u, v}).arrow_mk_iso_iff
    (Arrow.isoOfNatIso forwardComparisonIso (Arrow.mk f))

/-- The original inverse retains the full canonical fibration class. -/
theorem toLeft_fibrations_iff {M N : Spectrum.{u, v}} (f : M ⟶ N) :
    fibrations Spectrum.{u, v} (carrierEquivalence.inverse.map f) ↔
      fibrations Spectrum.{u, v} f :=
  (fibrations Spectrum.{u, v}).arrow_mk_iso_iff
    (Arrow.isoOfNatIso inverseComparisonIso (Arrow.mk f))

/-- Forward conversion retains the complete canonical trivial-fibration class. -/
theorem toRight_trivialFibrations_iff {M N : Spectrum.{u, v}} (f : M ⟶ N) :
    trivialFibrations Spectrum.{u, v} (carrierEquivalence.functor.map f) ↔
      trivialFibrations Spectrum.{u, v} f :=
  (trivialFibrations Spectrum.{u, v}).arrow_mk_iso_iff
    (Arrow.isoOfNatIso forwardComparisonIso (Arrow.mk f))

/-- Inverse conversion retains the complete canonical trivial-fibration class. -/
theorem toLeft_trivialFibrations_iff {M N : Spectrum.{u, v}} (f : M ⟶ N) :
    trivialFibrations Spectrum.{u, v} (carrierEquivalence.inverse.map f) ↔
      trivialFibrations Spectrum.{u, v} f :=
  (trivialFibrations Spectrum.{u, v}).arrow_mk_iso_iff
    (Arrow.isoOfNatIso inverseComparisonIso (Arrow.mk f))

/-- Every canonical cofibration is preserved and reflected by the full forward conversion. -/
theorem toRight_cofibrations_iff {M N : Spectrum.{u, v}} (f : M ⟶ N) :
    cofibrations Spectrum.{u, v} (carrierEquivalence.functor.map f) ↔
      cofibrations Spectrum.{u, v} f :=
  (cofibrations Spectrum.{u, v}).arrow_mk_iso_iff
    (Arrow.isoOfNatIso forwardComparisonIso (Arrow.mk f))

/-- The full inverse retains the entire canonical cofibration class. -/
theorem toLeft_cofibrations_iff {M N : Spectrum.{u, v}} (f : M ⟶ N) :
    cofibrations Spectrum.{u, v} (carrierEquivalence.inverse.map f) ↔
      cofibrations Spectrum.{u, v} f :=
  (cofibrations Spectrum.{u, v}).arrow_mk_iso_iff
    (Arrow.isoOfNatIso inverseComparisonIso (Arrow.mk f))

/-- The actual forward sphere action retains every canonical trivial cofibration. -/
theorem toRight_trivialCofibrations_iff {M N : Spectrum.{u, v}} (f : M ⟶ N) :
    trivialCofibrations Spectrum.{u, v} (carrierEquivalence.functor.map f) ↔
      trivialCofibrations Spectrum.{u, v} f :=
  (trivialCofibrations Spectrum.{u, v}).arrow_mk_iso_iff
    (Arrow.isoOfNatIso forwardComparisonIso (Arrow.mk f))

/-- The actual inverse sphere action retains every canonical trivial cofibration. -/
theorem toLeft_trivialCofibrations_iff {M N : Spectrum.{u, v}} (f : M ⟶ N) :
    trivialCofibrations Spectrum.{u, v} (carrierEquivalence.inverse.map f) ↔
      trivialCofibrations Spectrum.{u, v} f :=
  (trivialCofibrations Spectrum.{u, v}).arrow_mk_iso_iff
    (Arrow.isoOfNatIso inverseComparisonIso (Arrow.mk f))

/-- The original conjugated forward adjunction is Quillen for the canonical model. -/
theorem toRight_isQuillenAdjunction :
    carrierEquivalence.{u, v}.toAdjunction.IsQuillenAdjunction :=
  Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (fun _ _ f hf => (toLeft_fibrations_iff f).mpr hf)
    (fun _ _ f hf => (toLeft_trivialFibrations_iff f).mpr hf)

/-- Its complete original inverse adjunction is Quillen for the same canonical model. -/
theorem toLeft_isQuillenAdjunction :
    carrierEquivalence.{u, v}.symm.toAdjunction.IsQuillenAdjunction :=
  Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (fun _ _ f hf => (toRight_fibrations_iff f).mpr hf)
    (fun _ _ f hf => (toRight_trivialFibrations_iff f).mpr hf)

/-- The entire original forward adjunct detects weak equivalences on the canonical carrier. -/
theorem toRight_homEquiv_weakEquivalences_iff (M N : Spectrum.{u, v})
    (f : carrierEquivalence.functor.obj M ⟶ N) :
    weakEquivalences Spectrum.{u, v} f ↔ weakEquivalences Spectrum.{u, v}
      (carrierEquivalence.toAdjunction.homEquiv M N f) := by
  rw [carrierEquivalence.toAdjunction.homEquiv_unit]
  letI : IsIso (carrierEquivalence.unitIso.hom.app M) :=
    (carrierEquivalence.unitIso.app M).isIso_hom
  exact (toLeft_weakEquivalences_iff f).symm.trans
    ((weakEquivalences Spectrum.{u, v}).cancel_left_of_respectsIso
      (X := M) (Y := carrierEquivalence.inverse.obj (carrierEquivalence.functor.obj M))
      (Z := carrierEquivalence.inverse.obj N)
      (carrierEquivalence.unitIso.hom.app M) (carrierEquivalence.inverse.map f)).symm

/-- The entire original inverse adjunct detects weak equivalences on the canonical carrier. -/
theorem toLeft_homEquiv_weakEquivalences_iff (M N : Spectrum.{u, v})
    (f : carrierEquivalence.inverse.obj M ⟶ N) :
    weakEquivalences Spectrum.{u, v} f ↔ weakEquivalences Spectrum.{u, v}
      (carrierEquivalence.symm.toAdjunction.homEquiv M N f) := by
  rw [carrierEquivalence.symm.toAdjunction.homEquiv_unit]
  letI : IsIso (carrierEquivalence.symm.unitIso.hom.app M) :=
    (carrierEquivalence.symm.unitIso.app M).isIso_hom
  exact (toRight_weakEquivalences_iff f).symm.trans
    ((weakEquivalences Spectrum.{u, v}).cancel_left_of_respectsIso
      (X := M) (Y := carrierEquivalence.functor.obj (carrierEquivalence.inverse.obj M))
      (Z := carrierEquivalence.functor.obj N)
      (carrierEquivalence.symm.unitIso.hom.app M) (carrierEquivalence.functor.map f)).symm

/-- Both native endpoints of the actual forward conversion use the canonical level model. -/
theorem toRight_isQuillenEquivalence :
    carrierEquivalence.{u, v}.toAdjunction.IsQuillenEquivalence := by
  let _ : carrierEquivalence.{u, v}.toAdjunction.IsQuillenAdjunction :=
    toRight_isQuillenAdjunction
  exact { homEquiv_weakEquivalence_iff := fun f => toRight_homEquiv_weakEquivalences_iff _ _ f }

/-- The original inverse is a Quillen equivalence on those same canonical endpoints. -/
theorem toLeft_isQuillenEquivalence :
    carrierEquivalence.{u, v}.symm.toAdjunction.IsQuillenEquivalence := by
  let _ : carrierEquivalence.{u, v}.symm.toAdjunction.IsQuillenAdjunction :=
    toLeft_isQuillenAdjunction
  exact { homEquiv_weakEquivalence_iff := fun f => toLeft_homEquiv_weakEquivalences_iff _ _ f }

end PointedCGWH.Spectra.Symmetric.LeftRightNativeModel.Canonical
