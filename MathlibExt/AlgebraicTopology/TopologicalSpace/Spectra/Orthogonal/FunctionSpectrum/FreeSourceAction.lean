/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRFreeSourceAction
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.FreeSource
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereOneComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.Delooping
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceRightModuleFreeEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceRightModuleFreeUnit

/-!
# Native orthogonal free-function action and shift comparison

The canonical enriched constructions supply the complete free-function action.
These wrappers specialize to the continuous orthogonal index and original sphere
module, retaining both actual source equivalence units and the full native delta.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open CategoryTheory.Enriched.SphereOperator
open scoped MonoidalClosed
universe uV vV uI vI

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.Internal

-- Compatibility names for the canonical enriched source constructions.
export CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Internal
  (shiftedCoefficientAction rightSphereAction_shift blockSwap_parameter cotensorCoefficientAction_uncurry
    cotensorSphereAction_uncurry cotensorSphereAction_parameter_uncurry)

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.Internal

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.Mapping

-- Compatibility names for the canonical enriched source constructions.
export CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Mapping
  (translationTargetIso_hom_component rawRightShiftDiagramIso_hom_component
    rawRightShiftRestrictionIso_hom_component sigma_twoInputs translatedValueIso translatedValueIso_sigma
    OutputCarrierIsoType outputCarrierIso outputCarrierIso_hom_component OutputSigmaProperty outputSigma
    sourceDeltaAction sourceDeltaValue sourceDeltaValue_parameter sourceDeltaValue_generator
    sourceDeltaValue_inverse sourceDeltaValue_translated)

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.Mapping

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.OriginalOperator

-- Compatibility names for the canonical enriched source constructions.
export CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.OriginalOperator
  (moduleFor moduleFor_sigma CarrierIsoType carrierIso carrier_hom_component LinearityProperty carrier_linear
    OutputIsoType outputIso)

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.OriginalOperator

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.OriginalOperator.Family

-- Compatibility names for the canonical enriched source constructions.
export CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.OriginalOperator.Family
  (OutputIsoType outputIso outputIsoReadback NativeOutputIsoType nativeOutputIso nativeOutputIso_hom
    nativeOutputIso_inv EvaluationDataType sourceFreeIso sourceIso NativeFreeOutputIsoType nativeFreeOutputIso
    NativeFreeUnitOutputIsoType nativeFreeUnitOutputIso coefficientCotensorIso
    NativeFreeCoefficientOutputIsoType nativeFreeCoefficientOutputIso DeltaComponentProperty
    deltaValue_component)

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.OriginalOperator.Family

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta

-- Compatibility names for the canonical enriched source constructions.
export CategoryTheory.Enriched.ModuleMappingR.FreeSourceAction.Mapping.CanonicalDelta
  (regularModule sphereMap sphereMap_evaluate regularEvaluationIso sourceDelta regularEvaluationIso_factory_heq
    regularEvaluationIso_inverse_carrier_heq regularEvaluationIso_inverse_carrier_eq actualSourceι_eq
    actualMappingπ_eq regularTranspose_point regularEvaluationIso_inv_ι regularEvaluationIso_inv_π
    sphereMap_generator sourceDelta_hom sourceDelta_parameter sourceDelta_component
    regularEvaluationIso_inv_π_assoc)

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta


universe u v

open CategoryTheory.Spectra CategoryTheory.Spectra.OrthogonalSourceRightModule

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.NativeModule

/-- The continuous isometry category used by the original orthogonal source. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original direct sum tensor on the continuous orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The pointed continuous enrichment of the original orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block symmetry of the continuous orthogonal index. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
/-- The continuous Day tensor on the original orthogonal spaces. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

attribute [local instance] Enriched.prodCategory
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

private abbrev d := OrthogonalIndex.enrichedMonoidalData.{u, v}
private abbrev b := OrthogonalIndex.enrichedSymmetricData.{u, v}
private abbrev S := orthogonalSphereFunctor.{u, v}
private abbrev L := orthogonalSphereMonoidalData.{u, v}
private abbrev B := orthogonalSphereBraidedData.{u, v}

open CanonicalSourceRightModuleActions CanonicalSourceRightModuleEquivalence
open EnrichedDayKernel ModuleMappingR

/-- The existing original module constructor uses the unchanged canonical sphere data. -/
abbrev originalModule (F : NativeDiagram.{u, v}) :=
  OriginalOperator.moduleFor d.{u, v} S.{u, v} L.{u, v} F
    (sphereTransformation F) (CanonicalSourceUnitCompatibility.original_source_unit F)
    (CanonicalSourceCoefficientCompatibility.original_source_assoc F)

/-- The constructed input is literally the original existing canonical source module. -/
theorem originalModule_eq (F : NativeDiagram.{u, v}) : originalModule F = toModule F := rfl

/-- The complete actual original shifted cotensor. -/
abbrev shiftedCotensor (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u, v}) :=
  cotensorObject X ((RightShift.shift r).obj F)

/-- The literal full source function ISO from the unchanged original input families. -/
def OutputIsoType (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u, v}) :=
  OriginalOperator.Family.OutputIsoType d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    sphereTransformation CanonicalSourceUnitCompatibility.original_source_unit
    CanonicalSourceCoefficientCompatibility.original_source_assoc r X F

/-- Construct the actual whole native source-module function ISO
inside its original family stage. -/
def outputIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u, v}) :
    OutputIsoType r X F :=
  OriginalOperator.Family.outputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    sphereTransformation CanonicalSourceUnitCompatibility.original_source_unit
    CanonicalSourceCoefficientCompatibility.original_source_assoc
    (fun H c a => sphereTransformation_component H (c, a))
    PointedCGWH.isSeparator_tensorUnit r X F

/-- The literal whole native operator-carrier output on the actual existing E functor. -/
def NativeOutputIsoType (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u, v}) :=
  OriginalOperator.Family.NativeOutputIsoType d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    sphereTransformation CanonicalSourceUnitCompatibility.original_source_unit
    CanonicalSourceCoefficientCompatibility.original_source_assoc equivalence.symm r X F

/-- The actual E-image of the constructed original function module, with the original E counit. -/
def nativeOutputIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u, v}) :
    NativeOutputIsoType r X F :=
  OriginalOperator.Family.nativeOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    sphereTransformation CanonicalSourceUnitCompatibility.original_source_unit
    CanonicalSourceCoefficientCompatibility.original_source_assoc
    (fun H c a => sphereTransformation_component H (c, a))
    equivalence.symm originalModule_eq PointedCGWH.isSeparator_tensorUnit r X F

/-- The whole original function object on the actual native free source. -/
def NativeFreeOutputIsoType (r : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (F : NativeDiagram.{u, v}) :=
  OriginalOperator.Family.NativeFreeOutputIsoType d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    sphereTransformation CanonicalSourceUnitCompatibility.original_source_unit
    CanonicalSourceCoefficientCompatibility.original_source_assoc equivalence.symm r X F

/-- Construct the whole native free-function ISO from original E/free/evaluation source data. -/
def nativeFreeOutputIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u, v}) :
    NativeFreeOutputIsoType r X F :=
  OriginalOperator.Family.nativeFreeOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    sphereTransformation CanonicalSourceUnitCompatibility.original_source_unit
    CanonicalSourceCoefficientCompatibility.original_source_assoc
    (fun H c a => sphereTransformation_component H (c, a)) equivalence.symm originalModule_eq
    CanonicalSourceRightModuleFreeEvaluation.evaluationComparison
    PointedCGWH.isSeparator_tensorUnit r X F

/-- The complete actual function spectrum from free S0 is the full coend right shift. -/
def NativeFreeZeroOutputIsoType (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :=
  OriginalOperator.Family.NativeFreeUnitOutputIsoType d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    sphereTransformation CanonicalSourceUnitCompatibility.original_source_unit
    CanonicalSourceCoefficientCompatibility.original_source_assoc equivalence.symm r F

/-- The original S0 function ISO keeps the complete chosen unit cotensor evaluation. -/
def nativeFreeZeroOutputIso (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :
    NativeFreeZeroOutputIsoType r F :=
  OriginalOperator.Family.nativeFreeUnitOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    sphereTransformation CanonicalSourceUnitCompatibility.original_source_unit
    CanonicalSourceCoefficientCompatibility.original_source_assoc
    (fun H c a => sphereTransformation_component H (c, a)) equivalence.symm originalModule_eq
    CanonicalSourceRightModuleFreeEvaluation.evaluationComparison
    PointedCGWH.isSeparator_tensorUnit r F

/-- The actual free representation one-sphere function identifies the original sphere-one loop. -/
def NativeFreeOneOutputIsoType (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :=
  OriginalOperator.Family.NativeFreeCoefficientOutputIsoType
    d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    sphereTransformation CanonicalSourceUnitCompatibility.original_source_unit
    CanonicalSourceCoefficientCompatibility.original_source_assoc equivalence.symm
    r (PointedCGWH.orthogonalSphere.{u, v} 1) PointedCGWH.sphereOne.{u, v} F

/-- The full original S1 function ISO uses the actual proved representation-sphere comparison. -/
def nativeFreeOneOutputIso (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :
    NativeFreeOneOutputIsoType r F :=
  OriginalOperator.Family.nativeFreeCoefficientOutputIso
    d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    sphereTransformation CanonicalSourceUnitCompatibility.original_source_unit
    CanonicalSourceCoefficientCompatibility.original_source_assoc
    (fun H c a => sphereTransformation_component H (c, a)) equivalence.symm originalModule_eq
    CanonicalSourceRightModuleFreeEvaluation.evaluationComparison PointedCGWH.isSeparator_tensorUnit
    r (PointedCGWH.orthogonalSphere.{u, v} 1) PointedCGWH.sphereOne.{u, v}
    orthogonalOneSphereIsoSphereOne F

/-- The actual native full structure transpose keeps the original
coefficient-first sphere action. -/
theorem comparison_source_action (r : OrthogonalIndex) (F : NativeDiagram.{u, v})
    (c : OrthogonalIndex) :
    component (Delooping.comparison r F) (OrthogonalOperatorIndex.ofIndex.{u, v} c) =
      MonoidalClosed.curry
        ((β_ (S.{u, v}.obj r)
          (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} c))).hom ≫
          SphereOperator.rightSphereAction d.{u, v} S.{u, v} L.{u, v} F c r) := by
  rw [Delooping.comparison_component, ShiftOmega.omegaMap_eq_adjoint]
  change MonoidalClosed.curry (RightShift.action F c (c + r) r (β_ r c).hom) = _
  exact congrArg MonoidalClosed.curry
    (RightShift.Internal.action_eq_braid d.{u, v} S.{u, v} L.{u, v} F c (c + r) r (β_ r c).hom)

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.NativeModule

open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat


open CategoryTheory.Spectra CategoryTheory.Spectra.OrthogonalSourceRightModule
namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.NativeCanonicalDelta
/-- The continuous isometry category used by the original orthogonal source. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original direct sum tensor on the continuous orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The pointed continuous enrichment of the original orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block symmetry of the continuous orthogonal index. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
/-- The continuous Day tensor on the original orthogonal spaces. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}
attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
private abbrev d := OrthogonalIndex.enrichedMonoidalData.{u, v}
private abbrev b := OrthogonalIndex.enrichedSymmetricData.{u, v}
private abbrev S := orthogonalSphereFunctor.{u, v}
private abbrev L := orthogonalSphereMonoidalData.{u, v}
private abbrev B := orthogonalSphereBraidedData.{u, v}
open CanonicalSourceRightModuleActions EnrichedDayKernel ModuleMappingR

/-- The complete actual regular representation-sphere source module. -/
abbrev regularModule := Mapping.CanonicalDelta.regularModule d.{u, v} S.{u, v} L.{u, v}

/-- The actual stock native source free-sphere map retains every original coefficient. -/
def sphereMap (r : OrthogonalIndex) := Mapping.CanonicalDelta.sphereMap d.{u, v} S.{u, v} L.{u, v} r

/-- The actual stock source delta goes into the full original free sphere Mapping_R object. -/
def SourceDeltaType (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :=
  toModule F ⟶ moduleObject d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r
      (S.{u, v}.obj r)) (toModule F)

/-- The actual sphere map and regular evaluation construct the complete native source morphism. -/
def sourceDelta (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) : SourceDeltaType r F :=
  Mapping.CanonicalDelta.sourceDelta d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r (toModule F)

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.NativeCanonicalDelta
