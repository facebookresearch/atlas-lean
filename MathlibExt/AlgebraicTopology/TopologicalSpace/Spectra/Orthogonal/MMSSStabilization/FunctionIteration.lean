/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Functor.CoaugmentationIteration
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeOrthogonalFreePairBifunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.NativeSourceComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.IterationMaps
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmashClosed
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmashUnit
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceFreeSmash
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.NegativeHom
import MathlibExt.CategoryTheory.Monoidal.Closed.InternalHomInterchange
import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeCoefficient
import MathlibExt.CategoryTheory.Monoidal.Closed.UnitEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.GenericSourcePowers
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.LiteralFunctionPredicates

/-!
# The genuine orthogonal free-source function-spectrum functor

The original translated right-module Mapping_R functor is carried through
the actual native/source equivalence. Its complete free-source output
isomorphism is natural on all original spectrum arrows. The full carrier,
right action, original free generator, target action, block isometry and
both equivalence maps remain in this comparison.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

section CurrentFullFreeSourceBindings


set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal
open scoped CategoryTheory.MonObj MonoidalClosed

section NativeFullSourceFamily
universe uNativePair vNativePair
open CategoryTheory.Spectra
attribute [local instance] SphereSmashStructure.indexCategory SphereSmashStructure.indexMonoidalCategory
  SphereSmashStructure.indexEnrichedOrdinaryCategory SphereSmashStructure.indexSymmetricCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativeFullSourceFamily

/-- The full actual native successor type retains the complete current source context. -/
def SuccessorType : Type _ :=
  ∀ n, FullSourceFreePair.SuccessorComponentType CanonicalSourceFreeSmash.pairData.{uNativePair, vNativePair}
    PointedCGWH.orthogonalSphere.{uNativePair, vNativePair} n

/-- The whole native component type uses the original source/E instance and its full coefficient functors. -/
abbrev SuccessorComponentType (n : ℕ) : Type _ :=
  FullSourceFreePair.SuccessorComponentType CanonicalSourceFreeSmash.pairData.{uNativePair, vNativePair}
    PointedCGWH.orthogonalSphere.{uNativePair, vNativePair} n

/-- The complete actual native family has exactly that independently written component type in every degree. -/
theorem component_type_original :
    SuccessorType.{uNativePair, vNativePair} = (∀ n, SuccessorComponentType.{uNativePair, vNativePair} n) := rfl

/-- The entire current native pair family is the independently stated actual source family. -/
def pairComparison : OrthogonalSourcePair.FunctorIsoFormulaType.{uNativePair, vNativePair} :=
  OrthogonalSourcePair.functorIso.{uNativePair, vNativePair}

/-- Both complete original native comparison maps are retained as one whole source-family value. -/
theorem pairComparison_original :
    pairComparison.{uNativePair, vNativePair} = OrthogonalSourcePair.functorIso.{uNativePair, vNativePair} := rfl

/-- The actual source coefficient comparison retains the same original sphere multiplication maps. -/
def coefficient (n : ℕ) :
    PointedCGWH.orthogonalSphere.{uNativePair, vNativePair}
        (CanonicalSourceFreeSmash.pairData.{uNativePair, vNativePair}.tensorIndex 1 n) ≅
      PointedCGWH.orthogonalSphere.{uNativePair, vNativePair} 1 ⊗
        PointedCGWH.orthogonalSphere.{uNativePair, vNativePair} n :=
  PointedCGWH.orthogonalSphereTensorIso.{uNativePair, vNativePair} 1 n

/-- Every original source degree is the same actual one-plus-n successor label. -/
theorem degree (n : ℕ) : CanonicalSourceFreeSmash.pairData.{uNativePair, vNativePair}.tensorIndex 1 n = n + 1 :=
  Nat.one_add n

/-- Both maps of every actual native successor use the complete original source pair family. -/
def successor : SuccessorType.{uNativePair, vNativePair} :=
  FullSourceFreePair.successor CanonicalSourceFreeSmash.pairData.{uNativePair, vNativePair}
    PointedCGWH.orthogonalSphere.{uNativePair, vNativePair}
    coefficient.{uNativePair, vNativePair} degree.{uNativePair, vNativePair}
    pairComparison.{uNativePair, vNativePair}

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativeFullSourceFamily
end NativeFullSourceFamily

end
end CurrentFullFreeSourceBindings

section NativeFreePowerSource
universe uP vP
open CategoryTheory MonoidalCategory MonoidalClosed
open scoped MonoidalClosed

open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativePowers

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits

/-- The original morphisms of the orthogonal operator category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original direct-sum tensor on the orthogonal operator category. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed enrichment on the orthogonal operator category. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block-swap symmetry on the orthogonal operator category. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
/-- The original selected tensor on the native orthogonal spectra. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}
/-- The selected closed structure on the original native orthogonal spectra. -/
local instance : MonoidalClosed CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmashClosed.monoidalClosed.{u, v}

/-- The original selected Day tensor on the orthogonal indexed spaces. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  SphereSmashStructure.dayMonoidalCategory.{u, v}
/-- The original block-swap symmetry for the selected orthogonal Day tensor. -/
local instance : SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  SphereSmashStructure.daySymmetricCategory.{u, v}
/-- The original representation-sphere monoid for these source modules. -/
local instance : MonObj OrthogonalSourceRightModule.sphereISpace.{u, v} :=
  SphereSmashStructure.sphereMonoid.{u, v}
/-- The original commutativity proof of the representation-sphere monoid. -/
local instance : IsCommMonObj OrthogonalSourceRightModule.sphereISpace.{u, v} :=
  SphereSmashStructure.sphereCommutativeMonoid.{u, v}
/-- The actual coequalizers used by the selected source module tensor. -/
local instance : HasCoequalizers (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  SphereSmashStructure.spaceCoequalizers.{u, v}
/-- The original selected tensor on the sphere source modules. -/
local instance : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.monoidalCategory.{u, v}

/-- The original native free representation sphere at every dimension. -/
abbrev sphereFree (n : ℕ) : CanonicalSourceSmash.Carrier.{u, v} :=
  Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} n)

/-- The actual native tensor unit is the original reconstructed regular sphere module. -/
def nativeUnitRegularIso :
    𝟙_ CanonicalSourceSmash.Carrier.{u, v} ≅
      CanonicalSourceRightModuleEquivalence.fromModuleFunctor.obj
        (RightModuleFree.regularObject OrthogonalSourceRightModule.sphereISpace.{u, v}) :=
  eqToIso CanonicalSourceSmash.tensorUnit_eq_source ≪≫
    CanonicalSourceSmash.sourceEquivalence.functor.mapIso
      (CanonicalSourceSmashUnit.TypedSource.sourceUnitIso SphereSmash.sourceData.{u, v})

/-- Both original E/free maps and original sphere-zero coefficient maps identify the actual zero source. -/
def freeZeroIso : 𝟙_ CanonicalSourceSmash.Carrier.{u, v} ≅ sphereFree.{u, v} 0 :=
  nativeUnitRegularIso ≪≫ CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso ≪≫
    (Free.functor (OrthogonalOperatorIndex.ofIndex.{u, v} 0)).mapIso
      PointedCGWH.orthogonalSphereUnitIso.{u, v}

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativePowers



section ActualNativePowerData
set_option autoImplicit false
noncomputable section
universe uTypedNativePower vTypedNativePower
open CategoryTheory MonoidalCategory
open CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
attribute [local instance] SphereSmashStructure.indexCategory SphereSmashStructure.indexMonoidalCategory
  SphereSmashStructure.indexEnrichedOrdinaryCategory SphereSmashStructure.indexSymmetricCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativeTypedFullPowerData

/-- The complete actual native data type keeps the original source context and every sphere coefficient. -/
abbrev DataType : Type _ :=
  TypedFullPowerData.Data CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower}

/-- Both actual native zero/source maps and all original native free-pair maps are bound before iteration. -/
def data : DataType.{uTypedNativePower, vTypedNativePower} :=
  TypedFullPowerData.ofFreePair
    CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower}
    NativePowers.freeZeroIso.{uTypedNativePower, vTypedNativePower}
    NativeFullSourceFamily.coefficient.{uTypedNativePower, vTypedNativePower}
    NativeFullSourceFamily.degree.{uTypedNativePower, vTypedNativePower}
    NativeFullSourceFamily.pairComparison.{uTypedNativePower, vTypedNativePower}

/-- The whole actual closed/free successor type is independently stated for every original source label. -/
abbrev SuccessorFunctionType (n : ℕ) : Type _ :=
  TypedFullPowerData.SuccessorFunctionType CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} n

/-- Every full native successor function map uses the same complete original source data. -/
def successorFunction : ∀ n, SuccessorFunctionType.{uTypedNativePower, vTypedNativePower} n :=
  TypedFullPowerData.successorFunction CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower}

/-- The same actual native zero maps are retained as a whole original source value. -/
theorem data_zero_original : data.{uTypedNativePower, vTypedNativePower}.zero =
    NativePowers.freeZeroIso.{uTypedNativePower, vTypedNativePower} := rfl

/-- The full original native tensor-power type at every representation degree. -/
abbrev PowerType (n : ℕ) : Type _ := TypedFullPowerData.PowerType
  CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} n
/-- The full original native function-iteration type at every representation degree. -/
abbrev FunctionType (n : ℕ) : Type _ := TypedFullPowerData.FunctionType
  CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} n
/-- Every original native source arrow to the selected tensor unit. -/
abbrev UnitArrowType : Type _ := TypedFullPowerData.UnitArrowType
  CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower}
/-- The complete original adjacent-degree native source-drop type. -/
abbrev DropType (n : ℕ) : Type _ := TypedFullPowerData.DropType
  CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} n

/-- All native source powers use the original complete free-family data. -/
def power : ∀ n, PowerType.{uTypedNativePower, vTypedNativePower} n := TypedFullPowerData.power
  CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower}
/-- All native function functors use those same original source powers and actual closed choice. -/
def function : ∀ n, FunctionType.{uTypedNativePower, vTypedNativePower} n := TypedFullPowerData.function
  CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower}
/-- Both native power comparison maps are retained before every original source function value. -/
def powerFunction : ∀ n, FunctionType.{uTypedNativePower, vTypedNativePower} n := TypedFullPowerData.powerFunction
  CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower}
/-- Every actual native source arrow keeps its complete original source-drop map family. -/
def drop (l : UnitArrowType.{uTypedNativePower, vTypedNativePower}) :
    ∀ n, DropType.{uTypedNativePower, vTypedNativePower} n := TypedFullPowerData.drop
  CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower} l

/-- The whole selected source context is the actual original canonical context. -/
theorem context_original :
    TypedFullPowerData.sourceContext CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower} =
      CanonicalSourceSmash.sourceContext.{uTypedNativePower, vTypedNativePower} := rfl

/-- The complete source object family is the exact original native free-sphere family. -/
theorem objects_original :
    (fun n => TypedFullPowerData.object CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
      PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} n) =
    (fun n => Free.object (OrthogonalOperatorIndex.ofIndex.{uTypedNativePower, vTypedNativePower} n)
      (PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} n)) := rfl


/-- The entire original native successor function type on the actual canonical source and free spheres. -/
abbrev OriginalSuccessorFunctionType : Type _ :=
  TypedFullPowerData.OriginalSuccessorFunctionFormula
    CanonicalSourceSmash.sourceContext.{uTypedNativePower, vTypedNativePower}
    NativePowers.sphereFree.{uTypedNativePower, vTypedNativePower}

/-- The entire original native source-power type on those same actual tensors and coefficient objects. -/
abbrev OriginalPowerType : Type _ :=
  TypedFullPowerData.OriginalPowerFormula
    CanonicalSourceSmash.sourceContext.{uTypedNativePower, vTypedNativePower}
    NativePowers.sphereFree.{uTypedNativePower, vTypedNativePower}

/-- The entire original native function-iteration type includes every degree and the full closed functors. -/
abbrev OriginalFunctionType : Type _ :=
  TypedFullPowerData.OriginalFunctionFormula
    CanonicalSourceSmash.sourceContext.{uTypedNativePower, vTypedNativePower}
    NativePowers.sphereFree.{uTypedNativePower, vTypedNativePower}

/-- The entire original native arrow domain uses the actual canonical tensor unit. -/
abbrev OriginalUnitArrowType : Type _ :=
  TypedFullPowerData.OriginalUnitArrowFormula
    CanonicalSourceSmash.sourceContext.{uTypedNativePower, vTypedNativePower}
    NativePowers.sphereFree.{uTypedNativePower, vTypedNativePower}

/-- Every original native source-drop type retains the full original free-spectrum endpoints. -/
abbrev OriginalDropType : Type _ :=
  TypedFullPowerData.OriginalDropFormula NativePowers.sphereFree.{uTypedNativePower, vTypedNativePower}

/-- All native successor function types are the same whole original family by the actual source
and object equalities. -/
theorem successorFunction_type_original :
    (∀ n, SuccessorFunctionType.{uTypedNativePower, vTypedNativePower} n) =
      OriginalSuccessorFunctionType.{uTypedNativePower, vTypedNativePower} :=
  (TypedFullPowerData.successorFunctionType_original
    CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower}).trans
      (congrArg₂ (fun source P => TypedFullPowerData.OriginalSuccessorFunctionFormula source P)
        context_original.{uTypedNativePower, vTypedNativePower} objects_original.{uTypedNativePower, vTypedNativePower})

/-- All native source-power types are the same whole original family with both complete source maps. -/
theorem power_type_original :
    (∀ n, PowerType.{uTypedNativePower, vTypedNativePower} n) =
      OriginalPowerType.{uTypedNativePower, vTypedNativePower} :=
  (TypedFullPowerData.powerType_original
    CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower}).trans
      (congrArg₂ (fun source P => TypedFullPowerData.OriginalPowerFormula source P)
        context_original.{uTypedNativePower, vTypedNativePower} objects_original.{uTypedNativePower, vTypedNativePower})

/-- All native function-iteration types are exactly the full original family on the actual canonical source. -/
theorem function_type_original :
    (∀ n, FunctionType.{uTypedNativePower, vTypedNativePower} n) =
      OriginalFunctionType.{uTypedNativePower, vTypedNativePower} :=
  (TypedFullPowerData.functionType_original
    CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower}).trans
      (congrArg₂ (fun source P => TypedFullPowerData.OriginalFunctionFormula source P)
        context_original.{uTypedNativePower, vTypedNativePower} objects_original.{uTypedNativePower, vTypedNativePower})

/-- Every native source-unit arrow has the complete original domain and actual original tensor unit. -/
theorem unitArrow_type_original :
    UnitArrowType.{uTypedNativePower, vTypedNativePower} =
      OriginalUnitArrowType.{uTypedNativePower, vTypedNativePower} :=
  (TypedFullPowerData.unitArrowType_original
    CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower}).trans
      (congrArg₂ (fun source P => TypedFullPowerData.OriginalUnitArrowFormula source P)
        context_original.{uTypedNativePower, vTypedNativePower} objects_original.{uTypedNativePower, vTypedNativePower})

/-- The whole native source-drop type family retains all original free-spectrum source and target objects. -/
theorem drop_type_original :
    (∀ n, DropType.{uTypedNativePower, vTypedNativePower} n) =
      OriginalDropType.{uTypedNativePower, vTypedNativePower} :=
  (TypedFullPowerData.dropType_original
    CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower}).trans
      (congrArg (fun P => TypedFullPowerData.OriginalDropFormula P)
        objects_original.{uTypedNativePower, vTypedNativePower})



/-- Every original native source unit and power degree retain both full original maps. -/
abbrev PowerDropFormula : Prop :=
  TypedFullPowerData.PowerDropCompatibility CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower}

/-- The original full native family supplies every source-power square before a degree is selected. -/
theorem powerDropFormula : PowerDropFormula.{uTypedNativePower, vTypedNativePower} :=
  TypedFullPowerData.powerDropCompatibility CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower}

/-- The complete native function square binds every source arrow, degree and target together. -/
abbrev PowerFunctionDropFormula : Prop :=
  TypedFullPowerData.PowerFunctionDropCompatibility
    CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower}

theorem powerFunctionDropFormula : PowerFunctionDropFormula.{uTypedNativePower, vTypedNativePower} :=
  TypedFullPowerData.powerFunctionDropCompatibility
    CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower}

/-- Both inverse maps retain the same entire source arrow, degree and native target families. -/
abbrev PowerFunctionDropInverseFormula : Prop :=
  TypedFullPowerData.PowerFunctionDropInverseCompatibility
    CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower}

theorem powerFunctionDropInverseFormula : PowerFunctionDropInverseFormula.{uTypedNativePower, vTypedNativePower} :=
  TypedFullPowerData.powerFunctionDropInverseCompatibility
    CanonicalSourceFreeSmash.pairData.{uTypedNativePower, vTypedNativePower}
    PointedCGWH.orthogonalSphere.{uTypedNativePower, vTypedNativePower} data.{uTypedNativePower, vTypedNativePower}


end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativeTypedFullPowerData
end
end ActualNativePowerData

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativePowers


attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits

/-- The original morphisms of the orthogonal operator category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original direct-sum tensor on the orthogonal operator category. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed enrichment on the orthogonal operator category. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block-swap symmetry on the orthogonal operator category. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
/-- The original selected tensor on the native orthogonal spectra. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}
/-- The selected closed structure on the original native orthogonal spectra. -/
local instance : MonoidalClosed CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmashClosed.monoidalClosed.{u, v}

/-- The original selected Day tensor on the orthogonal indexed spaces. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  SphereSmashStructure.dayMonoidalCategory.{u, v}
/-- The original block-swap symmetry for the selected orthogonal Day tensor. -/
local instance : SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  SphereSmashStructure.daySymmetricCategory.{u, v}
/-- The original representation-sphere monoid for these source modules. -/
local instance : MonObj OrthogonalSourceRightModule.sphereISpace.{u, v} :=
  SphereSmashStructure.sphereMonoid.{u, v}
/-- The original commutativity proof of the representation-sphere monoid. -/
local instance : IsCommMonObj OrthogonalSourceRightModule.sphereISpace.{u, v} :=
  SphereSmashStructure.sphereCommutativeMonoid.{u, v}
/-- The actual coequalizers used by the selected source module tensor. -/
local instance : HasCoequalizers (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  SphereSmashStructure.spaceCoequalizers.{u, v}
/-- The original selected tensor on the sphere source modules. -/
local instance originalSourceModuleMonoidal : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.monoidalCategory.{u, v}

/-- Both ordered sphere coefficient maps retain the actual one-add index transport. -/
def spherePrefixIso (n : ℕ) :
    PointedCGWH.orthogonalSphere.{u, v} (n + 1) ≅
      PointedCGWH.orthogonalSphere.{u, v} 1 ⊗ PointedCGWH.orthogonalSphere.{u, v} n :=
  eqToIso (congrArg (PointedCGWH.orthogonalSphere.{u, v}) (Nat.one_add n).symm) ≪≫
    PointedCGWH.orthogonalSphereTensorIso.{u, v} 1 n

/-- The entire canonical native free pair identifies the actual successor free sphere. -/
def freeSuccessorIso (n : ℕ) : NativeFullSourceFamily.SuccessorComponentType.{u, v} n :=
  NativeFullSourceFamily.successor.{u, v} n

/-- The full successor function spectrum uses the two actual original source maps and currying. -/
def freeSuccessorFunctionIso (n : ℕ) : NativeTypedFullPowerData.SuccessorFunctionType.{u, v} n :=
  NativeTypedFullPowerData.successorFunction.{u, v} n

/-- The entire actual free-zero function spectrum is the original closed unit functor. -/
def freeZeroFunctionIso : ihom (sphereFree.{u, v} 0) ≅ 𝟭 CanonicalSourceSmash.Carrier.{u, v} :=
  (MonoidalClosed.internalHom (C := CanonicalSourceSmash.Carrier.{u, v})).mapIso
    freeZeroIso.op ≪≫ MonoidalClosed.unitNatIso.symm

/-- Genuine free products and full currying identify every actual F_n(S^n) function functor. -/
def freeFunctionIterationIso : ∀ n, NativeTypedFullPowerData.FunctionType.{u, v} n :=
  NativeTypedFullPowerData.function.{u, v}

/-- Every complete original native target arrow is retained by the forward function comparison. -/
theorem freeFunctionIterationIso_hom_naturality (n : ℕ)
    {X Y : CanonicalSourceSmash.Carrier.{u, v}} (f : X ⟶ Y) :
    (ihom (sphereFree n)).map f ≫ (freeFunctionIterationIso n).hom.app Y =
      (freeFunctionIterationIso n).hom.app X ≫
        (Functor.Iteration.iterate (ihom (sphereFree 1)) n).map f :=
  (freeFunctionIterationIso n).hom.naturality f

/-- Every complete original native target arrow is retained by the inverse function comparison. -/
theorem freeFunctionIterationIso_inv_naturality (n : ℕ)
    {X Y : CanonicalSourceSmash.Carrier.{u, v}} (f : X ⟶ Y) :
    (Functor.Iteration.iterate (ihom (sphereFree 1)) n).map f ≫
        (freeFunctionIterationIso n).inv.app Y =
      (freeFunctionIterationIso n).inv.app X ≫ (ihom (sphereFree n)).map f :=
  (freeFunctionIterationIso n).inv.naturality f

/-- Actual zero and successor free products identify every whole tensor source power. -/
def freePowerIso : ∀ n, NativeTypedFullPowerData.PowerType.{u, v} n :=
  NativeTypedFullPowerData.power.{u, v}

/-- An actual source arrow to the unit deletes the original first free sphere factor. -/
def familySourceDrop (l : NativeTypedFullPowerData.UnitArrowType.{u, v}) (n : ℕ) :
    NativeTypedFullPowerData.DropType.{u, v} n := NativeTypedFullPowerData.drop.{u, v} l n

/-- The entire actual free-family comparison keeps both source-power maps and original currying. -/
def freePowerFunctionIso (n : ℕ) : NativeTypedFullPowerData.FunctionType.{u, v} n :=
  NativeTypedFullPowerData.powerFunction.{u, v} n

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativePowers


section NativeOriginalPowerCompatibilityReadbacks
noncomputable section
universe uNativePowerReadback vNativePowerReadback
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed
attribute [local instance]
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexMonoidalCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexEnrichedOrdinaryCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexSymmetricCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativeTypedFullPowerData
/-- The actual original canonical tensor dictionary used by both full getter predicates. -/
local instance powerReadbackMonoidal :
    MonoidalCategory CanonicalSourceSmash.Carrier.{uNativePowerReadback, vNativePowerReadback} :=
  CanonicalSourceSmash.monoidalCategory.{uNativePowerReadback, vNativePowerReadback}
/-- The actual original selected closed dictionary used by both full getter predicates. -/
local instance powerReadbackClosed :
    MonoidalClosed CanonicalSourceSmash.Carrier.{uNativePowerReadback, vNativePowerReadback} :=
  CanonicalSourceSmashClosed.monoidalClosed.{uNativePowerReadback, vNativePowerReadback}

/-- The entire original public native power family is the same whole original-data value. -/
theorem power_value_original : NativePowers.freePowerIso.{uNativePowerReadback, vNativePowerReadback} =
    power.{uNativePowerReadback, vNativePowerReadback} := rfl

/-- The complete original public source-drop family retains every actual source arrow and every degree. -/
theorem drop_value_original :
    (fun (l : UnitArrowType.{uNativePowerReadback, vNativePowerReadback}) n =>
      NativePowers.familySourceDrop.{uNativePowerReadback, vNativePowerReadback} l n) =
        drop.{uNativePowerReadback, vNativePowerReadback} := rfl

/-- The entire original public power-function family retains both original function maps before evaluation. -/
theorem powerFunction_value_original :
    (fun n => NativePowers.freePowerFunctionIso.{uNativePowerReadback, vNativePowerReadback} n) =
      powerFunction.{uNativePowerReadback, vNativePowerReadback} := rfl

/-- The independent complete native power-drop formula keeps all original source arrows, degrees and both power maps. -/
abbrev OriginalPowerDropFormula : Prop :=
  let P := NativePowers.sphereFree.{uNativePowerReadback, vNativePowerReadback}
  let p := NativePowers.freePowerIso.{uNativePowerReadback, vNativePowerReadback}
  let d := NativePowers.familySourceDrop.{uNativePowerReadback, vNativePowerReadback}
  ∀ l : P 1 ⟶ 𝟙_ CanonicalSourceSmash.Carrier.{uNativePowerReadback, vNativePowerReadback},
    Powers.FullCompatibility.PowerDrop (P 1) P p (d l) l

/-- The original complete forward word uses the public native function and drop families
at the exact closed source context already used by their full native function types. -/
abbrev OriginalPowerFunctionDropFormula : Prop :=
  let c := CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
  let source := TypedFullPowerData.sourceContext c
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  let P := NativePowers.sphereFree.{uNativePowerReadback, vNativePowerReadback}
  let Fn := ∀ n, FunctionType.{uNativePowerReadback, vNativePowerReadback} n
  let DropFn := UnitArrowType.{uNativePowerReadback, vNativePowerReadback} →
    ∀ n, DropType.{uNativePowerReadback, vNativePowerReadback} n
  let originalP : Fn := NativePowers.freePowerFunctionIso.{uNativePowerReadback, vNativePowerReadback}
  let originalD : DropFn := NativePowers.familySourceDrop.{uNativePowerReadback, vNativePowerReadback}
  let formula : Fn → DropFn → Prop := TypedFullPowerData.LiteralFunctionDropFormula source P
  formula originalP originalD

/-- The independent inverse word retains both public native inverse maps and all l, n and X. -/
abbrev OriginalPowerFunctionDropInverseFormula : Prop :=
  let c := CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
  let source := TypedFullPowerData.sourceContext c
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  let P := NativePowers.sphereFree.{uNativePowerReadback, vNativePowerReadback}
  let Fn := ∀ n, FunctionType.{uNativePowerReadback, vNativePowerReadback} n
  let DropFn := UnitArrowType.{uNativePowerReadback, vNativePowerReadback} →
    ∀ n, DropType.{uNativePowerReadback, vNativePowerReadback} n
  let originalP : Fn := NativePowers.freePowerFunctionIso.{uNativePowerReadback, vNativePowerReadback}
  let originalD : DropFn := NativePowers.familySourceDrop.{uNativePowerReadback, vNativePowerReadback}
  let formula : Fn → DropFn → Prop := TypedFullPowerData.LiteralFunctionDropInverseFormula source P
  formula originalP originalD

/-- The first link stores the full generic equality at the exact native data family. -/
theorem powerFunctionDropFormula_literal :
    PowerFunctionDropFormula.{uNativePowerReadback, vNativePowerReadback} =
      TypedFullPowerData.LiteralPowerFunctionDropFormula
        CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
        PointedCGWH.orthogonalSphere.{uNativePowerReadback, vNativePowerReadback}
        data.{uNativePowerReadback, vNativePowerReadback} :=
  (TypedFullPowerData.literalPowerFunctionDropFormula_eq
    CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
    PointedCGWH.orthogonalSphere.{uNativePowerReadback, vNativePowerReadback}
    data.{uNativePowerReadback, vNativePowerReadback}).symm

/-- The inverse first link stores the same full original source and target families. -/
theorem powerFunctionDropInverseFormula_literal :
    PowerFunctionDropInverseFormula.{uNativePowerReadback, vNativePowerReadback} =
      TypedFullPowerData.LiteralPowerFunctionDropInverseFormula
        CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
        PointedCGWH.orthogonalSphere.{uNativePowerReadback, vNativePowerReadback}
        data.{uNativePowerReadback, vNativePowerReadback} :=
  (TypedFullPowerData.literalPowerFunctionDropInverseFormula_eq
    CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
    PointedCGWH.orthogonalSphere.{uNativePowerReadback, vNativePowerReadback}
    data.{uNativePowerReadback, vNativePowerReadback}).symm


/-- The complete stored native forward predicate, at the same original object
family and selected closed context as the public getter predicate. -/
def StoredNativePowerFunctionDropFormula : Prop :=
  let c := CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
  let source := TypedFullPowerData.sourceContext c
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  TypedFullPowerData.LiteralFunctionDropFormula source NativePowers.sphereFree
    powerFunction.{uNativePowerReadback, vNativePowerReadback} drop.{uNativePowerReadback, vNativePowerReadback}

/-- The stored inverse predicate retains the full same function and drop
families, with every original l, n and X still inside the literal predicate. -/
def StoredNativePowerFunctionDropInverseFormula : Prop :=
  let c := CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
  let source := TypedFullPowerData.sourceContext c
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  TypedFullPowerData.LiteralFunctionDropInverseFormula source NativePowers.sphereFree
    powerFunction.{uNativePowerReadback, vNativePowerReadback} drop.{uNativePowerReadback, vNativePowerReadback}

/-- This full data equality is independently stated before the getter proof.
The two operands share the original source, object family and complete function/drop types. -/
def NativePowerFunctionGetterEqualityType : Prop :=
  let c := CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
  let source := TypedFullPowerData.sourceContext c
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  let P := NativePowers.sphereFree.{uNativePowerReadback, vNativePowerReadback}
  let Fn := ∀ n, FunctionType.{uNativePowerReadback, vNativePowerReadback} n
  let DropFn := UnitArrowType.{uNativePowerReadback, vNativePowerReadback} →
    ∀ n, DropType.{uNativePowerReadback, vNativePowerReadback} n
  let formula : Fn → DropFn → Prop := TypedFullPowerData.LiteralFunctionDropFormula source P
  let p : Fn := powerFunction.{uNativePowerReadback, vNativePowerReadback}
  let d : DropFn := drop.{uNativePowerReadback, vNativePowerReadback}
  let originalP : Fn := NativePowers.freePowerFunctionIso.{uNativePowerReadback, vNativePowerReadback}
  let originalD : DropFn := NativePowers.familySourceDrop.{uNativePowerReadback, vNativePowerReadback}
  formula p d = formula originalP originalD

/-- The inverse data equality has the same entire original types and getters. -/
def NativePowerFunctionGetterInverseEqualityType : Prop :=
  let c := CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
  let source := TypedFullPowerData.sourceContext c
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  let P := NativePowers.sphereFree.{uNativePowerReadback, vNativePowerReadback}
  let Fn := ∀ n, FunctionType.{uNativePowerReadback, vNativePowerReadback} n
  let DropFn := UnitArrowType.{uNativePowerReadback, vNativePowerReadback} →
    ∀ n, DropType.{uNativePowerReadback, vNativePowerReadback} n
  let formula : Fn → DropFn → Prop := TypedFullPowerData.LiteralFunctionDropInverseFormula source P
  let p : Fn := powerFunction.{uNativePowerReadback, vNativePowerReadback}
  let d : DropFn := drop.{uNativePowerReadback, vNativePowerReadback}
  let originalP : Fn := NativePowers.freePowerFunctionIso.{uNativePowerReadback, vNativePowerReadback}
  let originalD : DropFn := NativePowers.familySourceDrop.{uNativePowerReadback, vNativePowerReadback}
  formula p d = formula originalP originalD

/-- Congruence uses the entire accepted getter equalities without selecting
any source arrow, degree or target object, or unfolding a recursive power family. -/
theorem nativePowerFunctionGetterEquality :
    NativePowerFunctionGetterEqualityType.{uNativePowerReadback, vNativePowerReadback} :=
  let c := CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
  let source := TypedFullPowerData.sourceContext c
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  let Fn := ∀ n, FunctionType.{uNativePowerReadback, vNativePowerReadback} n
  let DropFn := UnitArrowType.{uNativePowerReadback, vNativePowerReadback} →
    ∀ n, DropType.{uNativePowerReadback, vNativePowerReadback} n
  let formula : Fn → DropFn → Prop :=
    TypedFullPowerData.LiteralFunctionDropFormula source NativePowers.sphereFree
  congrArg₂ formula
    powerFunction_value_original.{uNativePowerReadback, vNativePowerReadback}.symm
    drop_value_original.{uNativePowerReadback, vNativePowerReadback}.symm

/-- Both complete original inverse getters satisfy the same whole data congruence. -/
theorem nativePowerFunctionGetterInverseEquality :
    NativePowerFunctionGetterInverseEqualityType.{uNativePowerReadback, vNativePowerReadback} :=
  let c := CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
  let source := TypedFullPowerData.sourceContext c
  letI := source.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed source
  let Fn := ∀ n, FunctionType.{uNativePowerReadback, vNativePowerReadback} n
  let DropFn := UnitArrowType.{uNativePowerReadback, vNativePowerReadback} →
    ∀ n, DropType.{uNativePowerReadback, vNativePowerReadback} n
  let formula : Fn → DropFn → Prop :=
    TypedFullPowerData.LiteralFunctionDropInverseFormula source NativePowers.sphereFree
  congrArg₂ formula
    powerFunction_value_original.{uNativePowerReadback, vNativePowerReadback}.symm
    drop_value_original.{uNativePowerReadback, vNativePowerReadback}.symm


/-- The prepared native supplier has the exact original full public power-drop proposition. -/
theorem powerDropFormula_original : PowerDropFormula.{uNativePowerReadback, vNativePowerReadback} =
    OriginalPowerDropFormula.{uNativePowerReadback, vNativePowerReadback} := rfl

/-- The checked first link and complete getter equality retain the full forward native formula. -/
theorem powerFunctionDropFormula_original :
    PowerFunctionDropFormula.{uNativePowerReadback, vNativePowerReadback} =
      OriginalPowerFunctionDropFormula.{uNativePowerReadback, vNativePowerReadback} :=
  @Eq.trans Prop
    PowerFunctionDropFormula.{uNativePowerReadback, vNativePowerReadback}
    (TypedFullPowerData.LiteralPowerFunctionDropFormula
      PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
      PointedCGWH.orthogonalSphere.{uNativePowerReadback, vNativePowerReadback}
      data.{uNativePowerReadback, vNativePowerReadback})
    OriginalPowerFunctionDropFormula.{uNativePowerReadback, vNativePowerReadback}
    powerFunctionDropFormula_literal.{uNativePowerReadback, vNativePowerReadback}
    nativePowerFunctionGetterEquality.{uNativePowerReadback, vNativePowerReadback}

/-- Both full native inverse maps follow through the same explicit complete predicates. -/
theorem powerFunctionDropInverseFormula_original :
    PowerFunctionDropInverseFormula.{uNativePowerReadback, vNativePowerReadback} =
      OriginalPowerFunctionDropInverseFormula.{uNativePowerReadback, vNativePowerReadback} :=
  @Eq.trans Prop
    PowerFunctionDropInverseFormula.{uNativePowerReadback, vNativePowerReadback}
    (TypedFullPowerData.LiteralPowerFunctionDropInverseFormula
      PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.pairData.{uNativePowerReadback, vNativePowerReadback}
      PointedCGWH.orthogonalSphere.{uNativePowerReadback, vNativePowerReadback}
      data.{uNativePowerReadback, vNativePowerReadback})
    OriginalPowerFunctionDropInverseFormula.{uNativePowerReadback, vNativePowerReadback}
    powerFunctionDropInverseFormula_literal.{uNativePowerReadback, vNativePowerReadback}
    nativePowerFunctionGetterInverseEquality.{uNativePowerReadback, vNativePowerReadback}


end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativeTypedFullPowerData
end
end NativeOriginalPowerCompatibilityReadbacks



section PreparedOriginalPowerProofs
namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativeTypedFullPowerData

/-- The full original power-drop statement follows from the entire source-data family. -/
theorem originalPowerDrop : OriginalPowerDropFormula.{u, v} :=
  (powerDropFormula_original.{u, v}).mp powerDropFormula.{u, v}

/-- Every original source arrow, source degree and target object retain the full function square. -/
theorem originalPowerFunctionDrop : OriginalPowerFunctionDropFormula.{u, v} :=
  (powerFunctionDropFormula_original.{u, v}).mp powerFunctionDropFormula.{u, v}

/-- Both inverse maps retain those exact entire original input families. -/
theorem originalPowerFunctionDropInverse : OriginalPowerFunctionDropInverseFormula.{u, v} :=
  (powerFunctionDropInverseFormula_original.{u, v}).mp powerFunctionDropInverseFormula.{u, v}

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativeTypedFullPowerData

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativePowers
/-- The original canonical tensor dictionary for the full native power-square proofs. -/
local instance sourceDropMonoidal : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}
/-- The original canonical closed dictionary for both full native function-square proofs. -/
local instance sourceDropClosed : MonoidalClosed CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmashClosed.monoidalClosed.{u, v}

/-- Both original source comparison maps preserve the literal whole power drop. -/
theorem familySourceDrop_freePowerIso
    (l : sphereFree.{u, v} 1 ⟶ 𝟙_ CanonicalSourceSmash.Carrier.{u, v}) (n : ℕ) :
    (freePowerIso (n + 1)).hom ≫ familySourceDrop l n =
      Powers.sourceDrop l n ≫ (freePowerIso n).hom :=
  NativeTypedFullPowerData.originalPowerDrop.{u, v} l n

/-- The complete contravariant function map preserves the actual free-family source drop. -/
theorem familySourceDrop_function_square :
    NativeTypedFullPowerData.OriginalPowerFunctionDropFormula.{u, v} :=
  NativeTypedFullPowerData.originalPowerFunctionDrop.{u, v}

/-- The inverse whole comparison uses the same original-input transition and source drop. -/
theorem familySourceDrop_function_square_inverse :
    NativeTypedFullPowerData.OriginalPowerFunctionDropInverseFormula.{u, v} :=
  NativeTypedFullPowerData.originalPowerFunctionDropInverse.{u, v}

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.NativePowers

end PreparedOriginalPowerProofs



end NativeFreePowerSource

section FullCategoryTransport
set_option autoImplicit false
universe uT vT uA vA uD vD
open CategoryTheory
namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.CategoryTransport

/-- The entire intermediate category and both original functors are transported before evaluation. -/
theorem compFunctorObjEq {A : Type uA} [Category.{vA} A] {C : Type uT}
    (c c' : Category.{vT} C) (hc : c = c')
    {D : Type uD} [Category.{vD} D]
    (P : letI := c; A ⥤ C) (P' : letI := c'; A ⥤ C)
    (R : letI := c; C ⥤ D) (R' : letI := c'; C ⥤ D)
    (hP : HEq P P') (hR : HEq R R') (X : A) :
    (letI := c; (P ⋙ R).obj X) = (letI := c'; R'.obj (P'.obj X)) := by
  cases hc
  let := c
  cases eq_of_heq hP
  cases eq_of_heq hR
  rfl

/-- Whole intermediate category, functors and transformations retain the actual whiskered component. -/
theorem whiskerLeftAppHEq {A : Type uA} [Category.{vA} A] {C : Type uT}
    (c c' : Category.{vT} C) (hc : c = c')
    {D : Type uD} [Category.{vD} D]
    (P : letI := c; A ⥤ C) (P' : letI := c'; A ⥤ C)
    (F G : letI := c; C ⥤ D) (F' G' : letI := c'; C ⥤ D)
    (hP : HEq P P') (hF : HEq F F') (hG : HEq G G')
    (η : letI := c; F ⟶ G) (η' : letI := c'; F' ⟶ G')
    (hη : HEq η η') (X : A) :
    HEq (letI := c; (Functor.whiskerLeft P η).app X)
      (letI := c'; η'.app (P'.obj X)) := by
  cases hc
  let := c
  cases eq_of_heq hP
  cases eq_of_heq hF
  cases eq_of_heq hG
  cases eq_of_heq hη
  rfl

/-- Evaluate the actual whole whiskered transformation without changing its source functors. -/
theorem whiskerLeftAppHEq_of_actual {A : Type uA} [Category.{vA} A]
    {C : Type uT} [Category.{vT} C] {D : Type uD} [Category.{vD} D]
    (P : A ⥤ C) {F G : C ⥤ D} (η : F ⟶ G) (X : A) :
    HEq ((Functor.whiskerLeft P η).app X) (η.app (P.obj X)) := by
  rfl

/-- Whole input/output object equalities retain the same original whiskered component. -/
theorem whiskerLeftAppHEq_of_objects {A : Type uA} [Category.{vA} A]
    {C : Type uT} [Category.{vT} C] {D : Type uD} [Category.{vD} D]
    (P : A ⥤ C) {F G : C ⥤ D} (η : F ⟶ G) (X : A) (Y : C)
    (hP : P.obj X = Y)
    (hF : (P ⋙ F).obj X = F.obj Y)
    (hG : (P ⋙ G).obj X = G.obj Y) :
    HEq ((Functor.whiskerLeft P η).app X) (η.app Y) := by
  cases hP
  rfl

/-- Entire source categories, original functors and transformations are transported before equality. -/
theorem sourceEquationHEq {A : Type uA} [Category.{vA} A] {C : Type uT}
    (c c' : Category.{vT} C) (hc : c = c')
    (P : letI := c; A ⥤ C) (P' : letI := c'; A ⥤ C)
    (R : letI := c; C ⥤ C) (R' : letI := c'; C ⥤ C)
    (H : A ⥤ A)
    (hP : HEq P P') (hR : HEq R R')
    (η : letI := c; 𝟭 C ⟶ R) (η' : letI := c'; 𝟭 C ⟶ R') (hη : HEq η η')
    (e : letI := c; P ⋙ R ≅ H ⋙ P) (e' : letI := c'; P' ⋙ R' ≅ H ⋙ P')
    (he : HEq e e') (δ : 𝟭 A ⟶ H)
    (h : letI := c; ∀ X,
      (Functor.whiskerLeft P η ≫ e.hom).app X = P.map (δ.app X)) :
    letI := c'; ∀ X,
      (Functor.whiskerLeft P' η' ≫ e'.hom).app X = P'.map (δ.app X) := by
  cases hc
  let := c
  cases eq_of_heq hP
  cases eq_of_heq hR
  cases eq_of_heq hη
  cases eq_of_heq he
  exact h

/-- Both original module categories are transported before either endofunctor or component. -/
theorem whiskerLeftEndoAppHEq {A : Type uA} [Category.{vA} A] {C : Type uT}
    (c c' : Category.{vT} C) (hc : c = c')
    (P : letI := c; A ⥤ C) (P' : letI := c'; A ⥤ C)
    (F G : letI := c; C ⥤ C) (F' G' : letI := c'; C ⥤ C)
    (hP : HEq P P') (hF : HEq F F') (hG : HEq G G')
    (η : letI := c; F ⟶ G) (η' : letI := c'; F' ⟶ G')
    (hη : HEq η η') (X : A) :
    HEq (letI := c; (Functor.whiskerLeft P η).app X)
      (letI := c'; η'.app (P'.obj X)) := by
  cases hc
  let := c
  cases eq_of_heq hP
  cases eq_of_heq hF
  cases eq_of_heq hG
  cases eq_of_heq hη
  rfl

/-- Whole original category equality preserves the composition of both complete original arrows. -/
theorem compHEq {C : Type uT} (c c' : Category.{vT} C) (hc : c = c')
    {A B T : C}
    (f : letI := c; A ⟶ B) (g : letI := c; B ⟶ T)
    (f' : letI := c'; A ⟶ B) (g' : letI := c'; B ⟶ T)
    (hf : HEq f f') (hg : HEq g g') :
    HEq (letI := c; f ≫ g) (letI := c'; f' ≫ g') := by
  cases hc
  let := c
  have hf' : f = f' := eq_of_heq hf
  have hg' : g = g' := eq_of_heq hg
  cases hf'
  cases hg'
  rfl

/-- Both complete isomorphism hom maps preserve the same whole category transport. -/
theorem isoHomHEq {C : Type uT} (c c' : Category.{vT} C) (hc : c = c')
    {A B : C} (e : letI := c; A ≅ B) (e' : letI := c'; A ≅ B)
    (he : HEq e e') :
    HEq (letI := c; e.hom) (letI := c'; e'.hom) := by
  cases hc
  let := c
  exact heq_of_eq (congrArg Iso.hom (eq_of_heq he))

/-- Whole original category equality retains the actual full NatIso component maps. -/
theorem natIsoHomAppHEq {A : Type uA} [Category.{vA} A]
    {C : Type uT} (c c' : Category.{vT} C) (hc : c = c')
    (F G : letI := c; A ⥤ C) (F' G' : letI := c'; A ⥤ C)
    (hF : HEq F F') (hG : HEq G G')
    (e : letI := c; F ≅ G) (e' : letI := c'; F' ≅ G')
    (he : HEq e e') (X : A) :
    HEq (letI := c; e.hom.app X) (letI := c'; e'.hom.app X) := by
  cases hc
  let := c
  have hF' : F = F' := eq_of_heq hF
  have hG' : G = G' := eq_of_heq hG
  cases hF'
  cases hG'
  exact heq_of_eq (congrArg (fun z => z.hom.app X) (eq_of_heq he))

/-- Both entire original natural transformations retain every actual component under category transport. -/
theorem natTransAppHEq {A : Type uA} [Category.{vA} A]
    {C : Type uT} (c c' : Category.{vT} C) (hc : c = c')
    (F G : letI := c; A ⥤ C) (F' G' : letI := c'; A ⥤ C)
    (hF : HEq F F') (hG : HEq G G')
    (e : letI := c; F ⟶ G) (e' : letI := c'; F' ⟶ G')
    (he : HEq e e') (X : A) :
    HEq (letI := c; e.app X) (letI := c'; e'.app X) := by
  cases hc
  let := c
  have hF' : F = F' := eq_of_heq hF
  have hG' : G = G' := eq_of_heq hG
  cases hF'
  cases hG'
  exact heq_of_eq (congrArg (fun z => z.app X) (eq_of_heq he))

/-- The actual source-output equation transports through the entire original category equality. -/
theorem sourceOutputHEq {C : Type uT} (c c' : Category.{vT} C) (hc : c = c')
    {A B T : C}
    (f : letI := c; A ⟶ B) (e : letI := c; B ≅ T)
    (f' : letI := c'; A ⟶ B) (e' : letI := c'; B ≅ T)
    (hf : HEq f f') (he : HEq e e')
    (g : letI := c'; A ⟶ T) (h : letI := c'; f' ≫ e'.hom = g) :
    HEq (letI := c; f ≫ e.hom) g := by
  cases hc
  let := c
  have hf' : f = f' := eq_of_heq hf
  have he' : e = e' := eq_of_heq he
  rw [hf', he']
  exact heq_of_eq h

/-- A complete original NatIso factory equality returns its supplied full component map. -/
theorem ofComponentsHomHEq {A : Type uA} [Category.{vA} A] {C : Type uT}
    (c c' : Category.{vT} C) (hc : c = c')
    (F G : letI := c; A ⥤ C) (F' G' : letI := c'; A ⥤ C)
    (hF : HEq F F') (hG : HEq G G')
    (a : letI := c; F ≅ G)
    (e : letI := c'; ∀ X : A, F'.obj X ≅ G'.obj X)
    (natural : letI := c'; ∀ {X Y : A} (f : X ⟶ Y),
      F'.map f ≫ (e Y).hom = (e X).hom ≫ G'.map f)
    (ha : HEq a (letI := c'; NatIso.ofComponents e (fun f => natural f)))
    (X : A) : HEq (letI := c; a.hom.app X) (letI := c'; (e X).hom) := by
  cases hc
  let := c
  cases eq_of_heq hF
  cases eq_of_heq hG
  exact heq_of_eq (congrArg (fun z => z.hom.app X) (eq_of_heq ha))


end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.CategoryTransport

end FullCategoryTransport

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Ambient

universe uAmbient vAmbient

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type uAmbient} [Category.{vAmbient} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  (R : C) [MonObj R] [IsCommMonObj R]

/-- Original regular evaluation and actual source precomposition form the full coaugmentation. -/
def sourceCoaugmentation {M : CommutativeModuleConversion.RightModule R}
    (f : M ⟶ RightModuleFree.regularObject R) :
    𝟭 (CommutativeModuleConversion.RightModule R) ⟶ RightModuleMappingEnd.functor R M :=
  (RightModuleMappingEnd.Regular.regularMappingNatIso R).inv ≫
    RightModuleMappingEnd.sourceNatTrans R f

/-- Every original component is the complete regular evaluation followed by source precomposition. -/
theorem sourceCoaugmentation_app {M : CommutativeModuleConversion.RightModule R}
    (f : M ⟶ RightModuleFree.regularObject R)
    (N : CommutativeModuleConversion.RightModule R) :
    (sourceCoaugmentation R f).app N =
      (RightModuleMappingEnd.Regular.regularMappingIso R N).inv ≫
        RightModuleMappingEnd.sourceMap R f N := rfl

/-- The faithful carrier keeps actual inverse evaluation and source precomposition. -/
theorem sourceCoaugmentationCarrier {M : CommutativeModuleConversion.RightModule R}
    (f : M ⟶ RightModuleFree.regularObject R)
    (N : CommutativeModuleConversion.RightModule R) :
    ((sourceCoaugmentation R f).app N).hom =
      (RightModuleMappingEnd.Regular.regularMappingIso R N).inv.hom ≫
        RightModuleMappingEnd.pre R f N := by
  have h := congrArg Mod.Hom.hom (sourceCoaugmentation_app R f N)
  exact h.trans
    ((Mod.comp_hom'
      (RightModuleMappingEnd.Regular.regularMappingIso R N).inv
      (RightModuleMappingEnd.sourceMap R f N)).trans
      (congrArg
        (fun q =>
          (RightModuleMappingEnd.Regular.regularMappingIso R N).inv.hom ≫ q)
        (RightModuleMappingEnd.sourceMap_hom R f N)))

/-- Whole source factories give the actual coaugmentation component without unfolding evaluation. -/
theorem sourceCoaugmentationComponentHEq
    {M : CommutativeModuleConversion.RightModule R}
    (f : M ⟶ RightModuleFree.regularObject R)
    (N : CommutativeModuleConversion.RightModule R)
    {A T : CommutativeModuleConversion.RightModule R}
    (hA : A = RightModuleMappingEnd.moduleObject R (RightModuleFree.regularObject R) N)
    (hT : T = RightModuleMappingEnd.moduleObject R M N)
    (e : A ≅ N)
    (he : HEq e (RightModuleMappingEnd.Regular.regularMappingIso R N))
    (g : A ⟶ T) (hg : HEq g (RightModuleMappingEnd.sourceMap R f N))
    (δ : N ⟶ T) (hδ : HEq δ (e.inv ≫ g)) :
    HEq δ ((sourceCoaugmentation R f).app N) := by
  cases hA
  cases hT
  have hEval : e =
      RightModuleMappingEnd.Regular.regularMappingIso R N := eq_of_heq he
  have hMap : g = RightModuleMappingEnd.sourceMap R f N := eq_of_heq hg
  have hActual : δ = e.inv ≫ g := eq_of_heq hδ
  rw [hActual, hEval, hMap]
  exact heq_of_eq (sourceCoaugmentation_app R f N).symm

/-- Transport the entire original coaugmentation along the given complete target-functor equality. -/
def transportedSourceCoaugmentation
    {M : CommutativeModuleConversion.RightModule R}
    (f : M ⟶ RightModuleFree.regularObject R)
    (G : CommutativeModuleConversion.RightModule R ⥤
      CommutativeModuleConversion.RightModule R)
    (hG : G = RightModuleMappingEnd.functor R M) :
    𝟭 (CommutativeModuleConversion.RightModule R) ⟶ G :=
  sourceCoaugmentation R f ≫ eqToHom hG.symm

/-- Whole transport keeps both the original component and its exact target object equality. -/
theorem transportedSourceCoaugmentation_app
    {M : CommutativeModuleConversion.RightModule R}
    (f : M ⟶ RightModuleFree.regularObject R)
    (G : CommutativeModuleConversion.RightModule R ⥤
      CommutativeModuleConversion.RightModule R)
    (hG : G = RightModuleMappingEnd.functor R M)
    (N : CommutativeModuleConversion.RightModule R) :
    (transportedSourceCoaugmentation R f G hG).app N ≫
        eqToHom (Functor.congr_obj hG N) =
      (sourceCoaugmentation R f).app N := by
  change ((sourceCoaugmentation R f).app N ≫ (eqToHom hG.symm).app N) ≫ _ = _
  rw [eqToHom_app, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Both whole transformation constructors retain the same complete original coaugmentation. -/
theorem transportedSourceCoaugmentation_heq
    {M : CommutativeModuleConversion.RightModule R}
    (f : M ⟶ RightModuleFree.regularObject R)
    (G : CommutativeModuleConversion.RightModule R ⥤
      CommutativeModuleConversion.RightModule R)
    (hG : G = RightModuleMappingEnd.functor R M) :
    HEq (transportedSourceCoaugmentation R f G hG) (sourceCoaugmentation R f) :=
  comp_eqToHom_heq _ hG.symm

/-- The transported complete module component is determined by its original faithful carrier. -/
theorem transportedSourceCoaugmentationCarrier
    {M : CommutativeModuleConversion.RightModule R}
    (f : M ⟶ RightModuleFree.regularObject R)
    (G : CommutativeModuleConversion.RightModule R ⥤
      CommutativeModuleConversion.RightModule R)
    (hG : G = RightModuleMappingEnd.functor R M)
    (N : CommutativeModuleConversion.RightModule R) :
    ((transportedSourceCoaugmentation R f G hG).app N).hom ≫
        (eqToHom (Functor.congr_obj hG N)).hom =
      (RightModuleMappingEnd.Regular.regularMappingIso R N).inv.hom ≫
        RightModuleMappingEnd.pre R f N := by
  have h := congrArg Mod.Hom.hom (transportedSourceCoaugmentation_app R f G hG N)
  exact (Mod.comp_hom' _ _).symm.trans (h.trans (sourceCoaugmentationCarrier R f N))

/-- Identity carrier transport identifies the same whole original module morphism. -/
theorem transportedSourceCoaugmentationCarrier_eq
    {M : CommutativeModuleConversion.RightModule R}
    (f : M ⟶ RightModuleFree.regularObject R)
    (G : CommutativeModuleConversion.RightModule R ⥤
      CommutativeModuleConversion.RightModule R)
    (hG : G = RightModuleMappingEnd.functor R M)
    (N : CommutativeModuleConversion.RightModule R)
    (hObj : (G.obj N).X = ((RightModuleMappingEnd.functor R M).obj N).X)
    (hCarrier : HEq (eqToHom (Functor.congr_obj hG N)).hom (𝟙 (G.obj N).X)) :
    HEq ((transportedSourceCoaugmentation R f G hG).app N).hom
      ((RightModuleMappingEnd.Regular.regularMappingIso R N).inv.hom ≫
        RightModuleMappingEnd.pre R f N) := by
  subst G
  have hG : RightModuleMappingEnd.functor R M = RightModuleMappingEnd.functor R M := rfl
  have h := transportedSourceCoaugmentationCarrier R f (RightModuleMappingEnd.functor R M) hG N
  have hActual : (eqToHom (Functor.congr_obj hG N)).hom =
      𝟙 ((RightModuleMappingEnd.functor R M).obj N).X :=
    eq_of_heq hCarrier
  have h' := (congrArg (fun q =>
    ((transportedSourceCoaugmentation R f (RightModuleMappingEnd.functor R M) hG).app N).hom ≫ q)
    hActual).symm.trans h
  exact heq_of_eq ((Category.comp_id _).symm.trans h')

/-- Actual source precomposition is the mate of the original balanced tensor source map. -/
theorem sourceMapCounit {M M' : CommutativeModuleConversion.RightModule R}
    (f : M' ⟶ M) (N : CommutativeModuleConversion.RightModule R) :
    letI := RightModuleFree.tensorMonoidal R
    (tensorLeft M').map (RightModuleMappingEnd.sourceMap R f N) ≫
        (RightModuleMappingEnd.leftAdjunction R M').counit.app N =
      (f ▷ (RightModuleMappingEnd.functor R M).obj N) ≫
        (RightModuleMappingEnd.leftAdjunction R M).counit.app N := by
  let := RightModuleFree.tensorMonoidal R
  let H := (RightModuleMappingEnd.functor R M).obj N
  let : Epi (RightModuleFree.relativeTensorπ R M' H) :=
    RightModuleFree.relativeTensorπ_epi R M' H
  apply Mod.hom_ext
  apply (cancel_epi (RightModuleFree.relativeTensorπ R M' H)).1
  rw [Mod.comp_hom', Mod.comp_hom']
  rw [← Category.assoc, RightModuleMappingEnd.tensorLeft_map_π, Category.assoc,
    RightModuleMappingEnd.leftAdjunction_counit_π]
  rw [← Category.assoc, RightModuleFree.relativeTensorWhiskerRight_π,
    Category.assoc, RightModuleMappingEnd.leftAdjunction_counit_π]
  exact (MonoidalClosed.uncurry_natural_left
    (RightModuleMappingEnd.sourceMap R f N).hom
    (RightModuleMappingEnd.ι R M' N)).symm.trans
      ((congrArg (MonoidalClosed.uncurry (C := C))
        (RightModuleMappingEnd.sourceMap_ι R f N)).trans
        (MonoidalClosed.uncurry_pre_app (C := C) N.X
          (RightModuleMappingEnd.ι R M N) f.hom))

/-- The original source natural transformation retains its actual complete map at each target. -/
theorem sourceNatTrans_app {M M' : CommutativeModuleConversion.RightModule R}
    (f : M' ⟶ M) (N : CommutativeModuleConversion.RightModule R) :
    (RightModuleMappingEnd.sourceNatTrans R f).app N =
      RightModuleMappingEnd.sourceMap R f N := rfl

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasEqualizers C] [HasCoequalizers C] in
/-- Original equality reflexivity retains the complete identity arrow. -/
theorem eqToHom_self (A : C) (p : A = A) : eqToHom p = 𝟙 A := rfl

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Ambient

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Internal

universe uV vV uI vI uC vC uD vD

attribute [local instance] Enriched.prodCategory
  EnrichedDayKernel.ColimitMonoidal.smallestColimits
  SphereModuleMappingEnd.moduleCategory
  MonoidalLeftAction.monoidalOppositeLeftAction

open EnrichedDayKernel ModuleMappingR

section WholeMaps

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Whole functor equalities retain the same transformation component without normalization. -/
theorem natTransAppHEq {F F' G G' : C ⥤ D}
    (hF : F = F') (hG : G = G')
    (η : F ⟶ G) (θ : F' ⟶ G') (hη : HEq η θ) (X : C) :
    HEq (η.app X) (θ.app X) := by
  cases hF
  cases hG
  exact heq_of_eq (congrArg (fun τ => τ.app X) (eq_of_heq hη))

/-- Whole isomorphism equality retains its actual inverse arrow at both source objects. -/
theorem inverseIsoMapHEq {M M' N N' : C} (hM : M = M') (hN : N = N')
    (e : M ≅ N) (e' : M' ≅ N') (hE : HEq e e') : HEq e.inv e'.inv := by
  cases hM
  cases hN
  exact heq_of_eq (congrArg Iso.inv (eq_of_heq hE))

/-- Two original inverse-evaluation factories and source maps retain their complete composite. -/
theorem inverseEvaluationSourceMapHEq {M M' N N' T T' : C}
    (hM : M = M') (hN : N = N') (hT : T = T')
    (e : M ≅ N) (e' : M' ≅ N') (hE : HEq e e')
    (g : M ⟶ T) (g' : M' ⟶ T') (hG : HEq g g') :
    HEq (e.inv ≫ g) (e'.inv ≫ g') :=
  heq_comp hN hM hT (inverseIsoMapHEq hM hN e e' hE) hG

/-- The exact whole component readback preserves the same equality transport at its target. -/
theorem coaugmentationComponent_eq {F G G' : C ⥤ D}
    (hG : G = G') (η : F ⟶ G) (θ : F ⟶ G') (hη : HEq η θ) (X : C)
    (δ : F.obj X ⟶ G'.obj X) (hδ : HEq δ (θ.app X)) :
    η.app X ≫ eqToHom (Functor.congr_obj hG X) = δ := by
  have h := natTransAppHEq rfl hG η θ hη X
  exact eq_of_heq ((comp_eqToHom_heq (η.app X) (Functor.congr_obj hG X)).trans
    (h.trans hδ.symm))

/-- Equal whole source and target module comparisons retain composition by the original map. -/
theorem postcomposeIsoHEq {A B B' T T' : C} (hB : B = B') (hT : T = T')
    (f : A ⟶ B) (e : B ≅ T) (e' : B' ≅ T') (he : HEq e e') :
    HEq (f ≫ e.hom) (f ≫ eqToHom hB ≫ e'.hom) := by
  cases hB
  cases hT
  have h : e = e' := eq_of_heq he
  rw [h, eqToHom_refl, Category.id_comp]

/-- The full source-output equation is preserved by both original whole factory identities. -/
theorem sourceOutput_of_factories {A B T : C}
    (f : A ⟶ B) (e e' : B ≅ T) (he : HEq e e')
    (g : A ⟶ T) (h : f ≫ e'.hom = g) : HEq (f ≫ e.hom) g := by
  have he' : e = e' := eq_of_heq he
  rw [he']
  exact heq_of_eq h

/-- Whole transformation equality is determined after the original target-functor transport. -/
theorem eq_transport_of_heq {F G G' : C ⥤ D} (hG : G = G')
    (η : F ⟶ G) (θ : F ⟶ G') (hη : HEq η θ) :
    η = θ ≫ eqToHom hG.symm := by
  cases hG
  have h : η = θ := eq_of_heq hη
  exact h.trans (Category.comp_id θ).symm

end WholeMaps

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)

/-- Original free-generator evaluation is target-natural after the entire block isometry. -/
theorem translatedValue_target (r : I) (X : V) {N N' : Module d S L}
    (g : N ⟶ N') (c : I) :
    component (post d b S L (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) g) c ≫
        (FunctionSpectrum.FreeSourceAction.Mapping.translatedValueIso d b S L r X N' c).hom =
      (FunctionSpectrum.FreeSourceAction.Mapping.translatedValueIso d b S L r X N c).hom ≫
        (ihom X).map (component (SphereModuleMappingEnd.moduleMap d S L g) (c ⊗ r)) := by
  let p := (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r X N c).hom
  let p' := (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d b S L r X N' c).hom
  let s := (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
    (β_ r c).hom
  let s' := (SphereModuleMappingEnd.diagram d S L N').toEnrichedFunctor.toOrdinaryFunctor.map
    (β_ r c).hom
  let q := component (SphereModuleMappingEnd.moduleMap d S L g) (r ⊗ c)
  let q' := component (SphereModuleMappingEnd.moduleMap d S L g) (c ⊗ r)
  have hv : component (post d b S L
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) g) c ≫ p' =
        p ≫ (ihom X).map q :=
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso_target d b S L r X g c
  have hs : s ≫ q' = q ≫ s' :=
    (ordinaryNatTrans (SphereModuleMappingEnd.moduleMap d S L g)).naturality (β_ r c).hom
  have hq : (ihom X).map q ≫ (ihom X).map s' =
      (ihom X).map s ≫ (ihom X).map q' :=
    ((ihom X).map_comp q s').symm.trans
      ((congrArg (ihom X).map hs.symm).trans ((ihom X).map_comp s q'))
  change _ ≫ (p' ≫ (ihom X).map s') = (p ≫ (ihom X).map s) ≫ (ihom X).map q'
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (ihom X).map s') hv).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => p ≫ k) hq).trans (Category.assoc _ _ _).symm)))

/-- The proved stock carrier comparison gives whole module naturality from original level maps. -/
theorem output_naturality (r : I) (X : V) {N N' T T' : Module d S L}
    (g : N ⟶ N') (t : T ⟶ T')
    (e : (functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)).obj N ≅ T)
    (e' : (functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)).obj N' ≅ T')
    (hObj : ∀ c : I, (SphereModuleMappingEnd.diagram d S L T).toEnrichedFunctor.obj c =
      (ihom X).obj ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r)))
    (hObj' : ∀ c : I, (SphereModuleMappingEnd.diagram d S L T').toEnrichedFunctor.obj c =
      (ihom X).obj ((SphereModuleMappingEnd.diagram d S L N').toEnrichedFunctor.obj (c ⊗ r)))
    (he : ∀ c : I, component (SphereModuleMappingEnd.moduleMap d S L e.hom) c ≫
      eqToHom (hObj c) =
        (FunctionSpectrum.FreeSourceAction.Mapping.translatedValueIso d b S L r X N c).hom)
    (he' : ∀ c : I, component (SphereModuleMappingEnd.moduleMap d S L e'.hom) c ≫
      eqToHom (hObj' c) =
        (FunctionSpectrum.FreeSourceAction.Mapping.translatedValueIso d b S L r X N' c).hom)
    (ht : ∀ c : I, component (SphereModuleMappingEnd.moduleMap d S L t) c ≫
      eqToHom (hObj' c) = eqToHom (hObj c) ≫
        (ihom X).map (component (SphereModuleMappingEnd.moduleMap d S L g) (c ⊗ r))) :
    (functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)).map g ≫
      e'.hom = e.hom ≫ t := by
  apply SphereModuleMappingEnd.moduleMap_ext d S L
  apply EnrichedFunctorCat.hom_ext
  intro c
  rw [SphereModuleMappingEnd.moduleMap_comp, SphereModuleMappingEnd.moduleMap_comp,
    component_comp, component_comp]
  apply (cancel_mono (eqToHom (hObj' c))).1
  rw [Category.assoc, he', Category.assoc, ht, ← Category.assoc,
    he, functor_map]
  exact translatedValue_target d b S L r X g c

/-- The whole Mapping_R functor chooses the original module object at every target. -/
theorem functor_obj (M N : Module d S L) :
    (functor d b S L B M).obj N = moduleObject d b S L B M N := rfl

/-- Read the original whole module comparison at the actual functor object. -/
def functorOutputIso {M N T : Module d S L}
    (e : moduleObject d b S L B M N ≅ T) : (functor d b S L B M).obj N ≅ T :=
  eqToIso (functor_obj d b S L B M N) ≪≫ e

/-- Whole module-factory equality retains both functor-object readback isomorphisms. -/
theorem functorOutputIso_heq {M N T : Module d S L}
    (e e' : moduleObject d b S L B M N ≅ T) (he : HEq e e') :
    HEq (functorOutputIso d b S L B e) (functorOutputIso d b S L B e') :=
  heq_of_eq (congrArg (fun e => functorOutputIso d b S L B e) (eq_of_heq he))

/-- Whole original source and target module equalities are eliminated before output projection. -/
theorem functorOutputIso_hom_of_whole_source
    {M M' N N' T T' : Module d S L}
    (hM : M = M') (hN : N = N') (hT : T = T')
    (e : moduleObject d b S L B M N ≅ T)
    (e' : moduleObject d b S L B M' N' ≅ T') (he : HEq e e') :
    HEq (functorOutputIso d b S L B e).hom
      (functorOutputIso d b S L B e').hom := by
  cases hM
  cases hN
  cases hT
  exact heq_of_eq (congrArg
    (fun a => (functorOutputIso d b S L B a).hom) (eq_of_heq he))

/-- The object calculation retains the original complete forward module carrier. -/
theorem functorOutputIso_hom {M N T : Module d S L}
    (e : moduleObject d b S L B M N ≅ T) :
    SphereModuleMappingEnd.moduleMap d S L (functorOutputIso d b S L B e).hom =
      SphereModuleMappingEnd.moduleMap d S L e.hom := by
  change SphereModuleMappingEnd.moduleMap d S L (𝟙 _ ≫ e.hom) = _
  rw [Category.id_comp]

/-- Both stock action maps retain the constructed carrier before and after the functor readback. -/
theorem outputIso_component (r : I) (X : V) (N T : Module d S L)
    (e : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.CarrierIsoType d b S L B r X N T)
    (hObj : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.TargetObjectLaw d S L r X N T)
    (hCarrier : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.CarrierLaw d b S L B
      r X N T e hObj)
    (hAction : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.TargetActionLaw d S L
      r X N T hObj) (c : I) :
    component (SphereModuleMappingEnd.moduleMap d S L
      (functorOutputIso d b S L B
        (FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.outputIso d b S L B
          r X N T e hObj hCarrier hAction)).hom) c ≫ eqToHom (hObj c) =
      (FunctionSpectrum.FreeSourceAction.Mapping.translatedValueIso d b S L r X N c).hom := by
  have h := functorOutputIso_hom d b S L B
    (FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.outputIso d b S L B
      r X N T e hObj hCarrier hAction)
  exact (congrArg (fun q => component q c ≫ eqToHom (hObj c)) h).trans (hCarrier c)

/-- Actual whole carrier and target-map calculations produce the complete free-source NatIso. -/
def freeOutputNatIso {A : Type uD} [Category.{vD} A]
    (r : I) (X : V) (P : A ⥤ Module d S L) (H : A ⥤ A)
    (e : ∀ F : A,
      (functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)).obj (P.obj F) ≅
        P.obj (H.obj F))
    (hObj : ∀ (F : A) (c : I),
      (SphereModuleMappingEnd.diagram d S L (P.obj (H.obj F))).toEnrichedFunctor.obj c =
        (ihom X).obj
          ((SphereModuleMappingEnd.diagram d S L (P.obj F)).toEnrichedFunctor.obj (c ⊗ r)))
    (he : ∀ (F : A) (c : I),
      component (SphereModuleMappingEnd.moduleMap d S L (e F).hom) c ≫ eqToHom (hObj F c) =
        (FunctionSpectrum.FreeSourceAction.Mapping.translatedValueIso d b S L r X (P.obj F) c).hom)
    (ht : ∀ {F G : A} (f : F ⟶ G) (c : I),
      component (SphereModuleMappingEnd.moduleMap d S L (P.map (H.map f))) c ≫
          eqToHom (hObj G c) = eqToHom (hObj F c) ≫
        (ihom X).map (component (SphereModuleMappingEnd.moduleMap d S L (P.map f)) (c ⊗ r))) :
    P ⋙ functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) ≅ H ⋙ P :=
  NatIso.ofComponents e (by
    intro F G f
    exact output_naturality d b S L B r X (P.map f) (P.map (H.map f))
      (e F) (e G) (hObj F) (hObj G) (he F) (he G) (ht f))

/-- Every whole free output comparison component is the original supplied lawful module map. -/
theorem freeOutputNatIso_hom_app {A : Type uD} [Category.{vD} A]
    (r : I) (X : V) (P : A ⥤ Module d S L) (H : A ⥤ A)
    (e : ∀ F : A,
      (functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)).obj (P.obj F) ≅
        P.obj (H.obj F))
    (hObj : ∀ (F : A) (c : I),
      (SphereModuleMappingEnd.diagram d S L (P.obj (H.obj F))).toEnrichedFunctor.obj c =
        (ihom X).obj
          ((SphereModuleMappingEnd.diagram d S L (P.obj F)).toEnrichedFunctor.obj (c ⊗ r)))
    (he : ∀ (F : A) (c : I),
      component (SphereModuleMappingEnd.moduleMap d S L (e F).hom) c ≫ eqToHom (hObj F c) =
        (FunctionSpectrum.FreeSourceAction.Mapping.translatedValueIso d b S L r X (P.obj F) c).hom)
    (ht : ∀ {F G : A} (f : F ⟶ G) (c : I),
      component (SphereModuleMappingEnd.moduleMap d S L (P.map (H.map f))) c ≫
          eqToHom (hObj G c) = eqToHom (hObj F c) ≫
        (ihom X).map (component (SphereModuleMappingEnd.moduleMap d S L (P.map f)) (c ⊗ r)))
    (F : A) :
    (freeOutputNatIso d b S L B r X P H e hObj he ht).hom.app F = (e F).hom := rfl

/-- Whole original category/functor/factory equality retains the supplied full module component. -/
theorem freeOutputNatIso_component_of_whole_factory {A : Type uD} [Category.{vD} A]
    (r : I) (X : V) (P : A ⥤ Module d S L) (H : A ⥤ A)
    (e : ∀ F : A,
      (functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)).obj (P.obj F) ≅
        P.obj (H.obj F))
    (hObj : ∀ (F : A) (c : I),
      (SphereModuleMappingEnd.diagram d S L (P.obj (H.obj F))).toEnrichedFunctor.obj c =
        (ihom X).obj
          ((SphereModuleMappingEnd.diagram d S L (P.obj F)).toEnrichedFunctor.obj (c ⊗ r)))
    (he : ∀ (F : A) (c : I),
      component (SphereModuleMappingEnd.moduleMap d S L (e F).hom) c ≫ eqToHom (hObj F c) =
        (FunctionSpectrum.FreeSourceAction.Mapping.translatedValueIso d b S L r X (P.obj F) c).hom)
    (ht : ∀ {F G : A} (f : F ⟶ G) (c : I),
      component (SphereModuleMappingEnd.moduleMap d S L (P.map (H.map f))) c ≫
          eqToHom (hObj G c) = eqToHom (hObj F c) ≫
        (ihom X).map (component (SphereModuleMappingEnd.moduleMap d S L (P.map f)) (c ⊗ r)))
    (c : Category (Module d S L))
    (hc : c = SphereModuleMappingEnd.moduleCategory d S L)
    (F₀ G₀ : letI := c; A ⥤ Module d S L)
    (hF : HEq F₀ (letI := SphereModuleMappingEnd.moduleCategory d S L
      P ⋙ functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X)))
    (hG : HEq G₀ (letI := SphereModuleMappingEnd.moduleCategory d S L; H ⋙ P))
    (a : letI := c; F₀ ≅ G₀)
    (ha : HEq a (letI := SphereModuleMappingEnd.moduleCategory d S L
      freeOutputNatIso d b S L B r X P H e hObj he ht)) (F : A) :
    HEq (letI := c; a.hom.app F)
      (letI := SphereModuleMappingEnd.moduleCategory d S L; (e F).hom) := by
  cases hc
  cases eq_of_heq hF
  cases eq_of_heq hG
  have h := eq_of_heq ha
  cases h
  exact heq_of_eq (freeOutputNatIso_hom_app d b S L B r X P H e hObj he ht F)

/-- Both source comparison maps act on the genuine whole Mapping_R target functor. -/
def sourceNatIso {M M' : Module d S L} (e : M ≅ M') :
    functor d b S L B M' ≅ functor d b S L B M :=
  NatIso.ofComponents (FunctionSpectrum.FreeSourceAction.OriginalOperator.Family.sourceIso
    d b S L B e) (by
      intro N N' g
      exact moduleSourceMap_naturality d b S L B e.hom g)

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The original free/evaluation functor chooses the same entire free right-module object. -/
theorem freeObject_eq (r : I) (X : V) :
    letI := ColimitMonoidal.monoidalCategory d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X =
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free
        (⟨S⟩ : EnrichedFunctorCat V I) r).obj X := rfl

/-- Original regular evaluation followed by actual source precomposition defines lambda-star. -/
def sourceLambda (r : I) : 𝟭 (Module d S L) ⟶
    functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)) := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  exact Ambient.sourceCoaugmentation (⟨S⟩ : EnrichedFunctorCat V I)
    (FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sphereMap d S L r)

/-- The original whole coaugmentation is the same generic regular-evaluation source factory. -/
theorem sourceLambdaFactoryHEq (r : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    HEq (sourceLambda d b S L B r)
      (Ambient.sourceCoaugmentation (⟨S⟩ : EnrichedFunctorCat V I)
        (FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sphereMap d S L r)) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  rfl

/-- The entire original initializer equals the same transported coaugmentation, before components. -/
theorem sourceLambdaFactoryEq (r : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    sourceLambda d b S L B r =
      Ambient.transportedSourceCoaugmentation (⟨S⟩ : EnrichedFunctorCat V I)
        (FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sphereMap d S L r)
        (functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)))
        (functor_eq_source d b S L B
          (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r))) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  exact eq_transport_of_heq
    (functor_eq_source d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)))
    (sourceLambda d b S L B r)
    (Ambient.sourceCoaugmentation (⟨S⟩ : EnrichedFunctorCat V I)
      (FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sphereMap d S L r))
    (sourceLambdaFactoryHEq d b S L B r)

/-- The full actual source arrow is the same original generic Mapping_R precomposition. -/
theorem moduleSourceMapFactoryHEq {M M' : Module d S L}
    (f : M' ⟶ M) (N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    HEq (moduleSourceMap d b S L B f N)
      (RightModuleMappingEnd.sourceMap (⟨S⟩ : EnrichedFunctorCat V I) f N) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  rfl

/-- The original entire source delta retains its two actual module-map factors. -/
theorem sourceDeltaFactoryHEq (r : I) (N : Module d S L) :
    HEq (FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sourceDelta d b S L B r N)
      ((FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.regularEvaluationIso
          d b S L B N).inv ≫
        moduleSourceMap d b S L B
          (FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sphereMap d S L r) N) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  rfl

/-- Whole source factories identify actual delta with the original coaugmentation component. -/
theorem sourceDeltaGenericHEq (r : I) (N : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := Closed.monoidalClosed d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    HEq (FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sourceDelta d b S L B r N)
      ((Ambient.transportedSourceCoaugmentation (⟨S⟩ : EnrichedFunctorCat V I)
        (FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sphereMap d S L r)
        (functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)))
        (functor_eq_source d b S L B
          (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)))).app N) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let M := CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)
  let A := FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.regularModule d S L
  let f := FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sphereMap d S L r
  have hM := moduleObject_eq_source d b S L B A N
  have hT := moduleObject_eq_source d b S L B M N
  apply heq_of_eq
  apply SphereModuleMappingEnd.moduleMap_ext d S L
  have hDelta := FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sourceDelta_hom
    d b S L B r N
  have hEval :=
    FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.regularEvaluationIso_inverse_carrier_eq
      d b S L B N
  have hFactory := sourceLambdaFactoryEq d b S L B r
  rw [hDelta, hEval]
  have hTransport : ((eqToHom (Functor.congr_obj (functor_eq_source d b S L B M) N)) :
      (functor d b S L B M).obj N ⟶
        (RightModuleMappingEnd.functor (⟨S⟩ : EnrichedFunctorCat V I) M).obj N).hom = 𝟙 _ := by
    rfl
  exact (eq_of_heq (Ambient.transportedSourceCoaugmentationCarrier_eq
    (⟨S⟩ : EnrichedFunctorCat V I) f (functor d b S L B M)
    (functor_eq_source d b S L B M) N rfl (heq_of_eq hTransport))).symm

/-- The whole module equality follows from the actual faithful source carrier. -/
theorem sourceLambda_app (r : I) (N : Module d S L) :
    (sourceLambda d b S L B r).app N ≫
        eqToHom (functor_obj d b S L B
          (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)) N) =
      FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sourceDelta d b S L B r N := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : SymmetricCategory (EnrichedFunctorCat V I) := BraidingMonoidal.symmetricCategory d b
  let : MonoidalClosed (EnrichedFunctorCat V I) := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let M := CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)
  let f := FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sphereMap d S L r
  have hF := functor_eq_source d b S L B M
  have hDelta := sourceDeltaGenericHEq d b S L B r N
  have hFactory := congrArg (fun τ => τ.app N) (sourceLambdaFactoryEq d b S L B r)
  have hBody : HEq (FunctionSpectrum.FreeSourceAction.Mapping.CanonicalDelta.sourceDelta
      d b S L B r N) ((sourceLambda d b S L B r).app N) :=
    hDelta.trans (heq_of_eq hFactory.symm)
  exact eq_of_heq ((comp_eqToHom_heq ((sourceLambda d b S L B r).app N)
    (functor_obj d b S L B M N)).trans hBody.symm)

/-- The complete original free-function output carries source precomposition to source delta. -/
theorem sourceLambda_output (r : I) (N T : Module d S L)
    (e : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.CarrierIsoType
      d b S L B r (S.obj r) N T)
    (hObj : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.TargetObjectLaw
      d S L r (S.obj r) N T)
    (hCarrier : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.CarrierLaw
      d b S L B r (S.obj r) N T e hObj)
    (hAction : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.TargetActionLaw
      d S L r (S.obj r) N T hObj) :
    (sourceLambda d b S L B r).app N ≫
        (functorOutputIso d b S L B
          (FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.outputIso d b S L B
            r (S.obj r) N T e hObj hCarrier hAction)).hom =
      FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.originalSourceComparison
        d b S L B r N T e hObj hCarrier hAction := by
  change (sourceLambda d b S L B r).app N ≫
    (eqToHom (functor_obj d b S L B
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r)) N) ≫
        (FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.outputIso d b S L B
          r (S.obj r) N T e hObj hCarrier hAction).hom) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫
      (FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.outputIso d b S L B
        r (S.obj r) N T e hObj hCarrier hAction).hom) (sourceLambda_app d b S L B r N))

/-- Whole original output-isomorphism equality retains the same complete source lambda square. -/
theorem sourceLambda_output_of_whole_iso (r : I) (N T : Module d S L)
    (e : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.CarrierIsoType
      d b S L B r (S.obj r) N T)
    (hObj : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.TargetObjectLaw
      d S L r (S.obj r) N T)
    (hCarrier : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.CarrierLaw
      d b S L B r (S.obj r) N T e hObj)
    (hAction : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.TargetActionLaw
      d S L r (S.obj r) N T hObj)
    (a : (functor d b S L B
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r))).obj N ≅ T)
    (ha : HEq a (functorOutputIso d b S L B
      (FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.outputIso d b S L B
        r (S.obj r) N T e hObj hCarrier hAction))) :
    HEq ((sourceLambda d b S L B r).app N ≫ a.hom)
      (FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.originalSourceComparison
        d b S L B r N T e hObj hCarrier hAction) := by
  have h := eq_of_heq ha
  cases h
  exact heq_of_eq (sourceLambda_output d b S L B r N T e hObj hCarrier hAction)

/-- Whole category, endpoint, coaugmentation and output factories are transported before composition. -/
theorem sourceLambda_output_of_whole_factories (r : I) (N T : Module d S L)
    (e : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.CarrierIsoType
      d b S L B r (S.obj r) N T)
    (hObj : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.TargetObjectLaw
      d S L r (S.obj r) N T)
    (hCarrier : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.CarrierLaw
      d b S L B r (S.obj r) N T e hObj)
    (hAction : FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.TargetActionLaw
      d S L r (S.obj r) N T hObj)
    (c : Category (Module d S L))
    (hc : c = SphereModuleMappingEnd.moduleCategory d S L)
    (N₀ T₀ N₁ T₁ : Module d S L)
    (hN₀ : N₀ = N) (hT₀ : T₀ = T) (hN₁ : N₁ = N) (hT₁ : T₁ = T)
    (R₀ : letI := c; Module d S L ⥤ Module d S L)
    (hR : HEq R₀ (letI := SphereModuleMappingEnd.moduleCategory d S L
      functor d b S L B (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r (S.obj r))))
    (η : letI := c; 𝟭 (Module d S L) ⟶ R₀)
    (hη : HEq η (letI := SphereModuleMappingEnd.moduleCategory d S L
      sourceLambda d b S L B r))
    (a : letI := c; R₀.obj N₀ ≅ T₀)
    (ha : HEq a (letI := SphereModuleMappingEnd.moduleCategory d S L
      functorOutputIso d b S L B
        (FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.outputIso d b S L B
          r (S.obj r) N T e hObj hCarrier hAction)))
    (f : letI := c; N₁ ⟶ T₁)
    (hf : HEq f (letI := SphereModuleMappingEnd.moduleCategory d S L
      FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.originalSourceComparison
        d b S L B r N T e hObj hCarrier hAction)) :
    HEq (letI := c; η.app N₀ ≫ a.hom) f := by
  cases hc
  cases hN₀
  cases hT₀
  cases hN₁
  cases hT₁
  cases eq_of_heq hR
  cases eq_of_heq hη
  cases eq_of_heq ha
  cases eq_of_heq hf
  exact heq_of_eq (sourceLambda_output d b S L B r N T e hObj hCarrier hAction)

/-- Every whole output NatIso built from actual free-module maps keeps the original lambda square. -/
theorem freeOutputNatIso_sourceLambda {A : Type uD} [Category.{vD} A]
    (r : I) (P : A ⥤ Module d S L) (H : A ⥤ A)
    (e : ∀ F : A, FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.CarrierIsoType
      d b S L B r (S.obj r) (P.obj F) (P.obj (H.obj F)))
    (hObj : ∀ F : A, FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.TargetObjectLaw
      d S L r (S.obj r) (P.obj F) (P.obj (H.obj F)))
    (hCarrier : ∀ F : A, FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.CarrierLaw
      d b S L B r (S.obj r) (P.obj F) (P.obj (H.obj F)) (e F) (hObj F))
    (hAction : ∀ F : A, FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.TargetActionLaw
      d S L r (S.obj r) (P.obj F) (P.obj (H.obj F)) (hObj F))
    (ht : ∀ {F G : A} (f : F ⟶ G) (c : I),
      component (SphereModuleMappingEnd.moduleMap d S L (P.map (H.map f))) c ≫
          eqToHom (hObj G c) = eqToHom (hObj F c) ≫
        (ihom (S.obj r)).map
          (component (SphereModuleMappingEnd.moduleMap d S L (P.map f)) (c ⊗ r)))
    (F : A) :
    (sourceLambda d b S L B r).app (P.obj F) ≫
      (freeOutputNatIso d b S L B r (S.obj r) P H
        (fun X => functorOutputIso d b S L B
          (FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.outputIso d b S L B
            r (S.obj r) (P.obj X) (P.obj (H.obj X))
            (e X) (hObj X) (hCarrier X) (hAction X))) hObj
        (fun X c => outputIso_component d b S L B r (S.obj r)
          (P.obj X) (P.obj (H.obj X)) (e X) (hObj X) (hCarrier X) (hAction X) c) ht).hom.app F =
      FunctionSpectrum.FreeSourceAction.Mapping.SourceStage.originalSourceComparison
        d b S L B r (P.obj F) (P.obj (H.obj F))
        (e F) (hObj F) (hCarrier F) (hAction F) := by
  exact sourceLambda_output d b S L B r (P.obj F) (P.obj (H.obj F))
    (e F) (hObj F) (hCarrier F) (hAction F)

section Carrier

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (E : C ≌ D) (R : C ⥤ C) (H : D ⥤ D)

/-- Both original equivalence functors carry the actual source coaugmentation. -/
def carryCoaugmentation (η : 𝟭 C ⟶ R) :
    𝟭 D ⟶ E.inverse ⋙ R ⋙ E.functor :=
  E.counitIso.inv ≫
    Functor.whiskerLeft E.inverse (Functor.whiskerRight η E.functor)

/-- Each whole carried component keeps the original inverse counit and source map. -/
theorem carryCoaugmentation_app (η : 𝟭 C ⟶ R) (X : D) :
    (carryCoaugmentation E R η).app X =
      E.counitIso.inv.app X ≫ E.functor.map (η.app (E.inverse.obj X)) := rfl

/-- The original source comparison is carried through both complete equivalence functors. -/
def carryOutputIso (F : D) (e : R.obj (E.inverse.obj F) ≅ E.inverse.obj (H.obj F)) :
    E.functor.obj (R.obj (E.inverse.obj F)) ≅ H.obj F :=
  E.functor.mapIso e ≪≫ E.counitIso.app (H.obj F)

/-- Complete source naturality and the original counit give naturality on every native arrow. -/
def carryOutputNatIso
    (e : E.inverse ⋙ R ≅ H ⋙ E.inverse) :
    E.inverse ⋙ R ⋙ E.functor ≅ H :=
  Functor.isoWhiskerRight e E.functor ≪≫
    Functor.associator H E.inverse E.functor ≪≫
    Functor.isoWhiskerLeft H E.counitIso ≪≫ H.rightUnitor

/-- Every full native output uses the original source map and the actual equivalence counit. -/
theorem carryOutputNatIso_hom_app (e : E.inverse ⋙ R ≅ H ⋙ E.inverse) (F : D) :
    (carryOutputNatIso E R H e).hom.app F =
      E.functor.map (e.hom.app F) ≫ E.counitIso.hom.app (H.obj F) := by
  simp only [carryOutputNatIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.rightUnitor_hom_app, Category.id_comp]
  exact congrArg (fun q => E.functor.map (e.hom.app F) ≫ q)
    (Category.comp_id (E.counitIso.hom.app (H.obj F)))

/-- Original source composition occurs between both actual equivalence counit factors. -/
theorem carryCoaugmentation_output_app (η : 𝟭 C ⟶ R)
    (e : E.inverse ⋙ R ≅ H ⋙ E.inverse) (X : D) :
    ((carryCoaugmentation E R η) ≫ (carryOutputNatIso E R H e).hom).app X =
      E.counitIso.inv.app X ≫
        E.functor.map (η.app (E.inverse.obj X) ≫ e.hom.app X) ≫
        E.counitIso.hom.app (H.obj X) := by
  rw [NatTrans.comp_app, carryCoaugmentation_app, carryOutputNatIso_hom_app]
  simp only [Functor.map_comp, Category.assoc]

/-- Both original counit words transfer an actual source equation to the whole native map. -/
theorem carryCoaugmentation_output_of_source (η : 𝟭 C ⟶ R)
    (e : E.inverse ⋙ R ≅ H ⋙ E.inverse) (δ : 𝟭 D ⟶ H)
    (hSource : ∀ X : D,
      η.app (E.inverse.obj X) ≫ e.hom.app X = E.inverse.map (δ.app X)) :
    carryCoaugmentation E R η ≫ (carryOutputNatIso E R H e).hom = δ := by
  apply NatTrans.ext
  funext X
  rw [carryCoaugmentation_output_app, hSource]
  have hNat := E.counitIso.hom.naturality (δ.app X)
  change E.functor.map (E.inverse.map (δ.app X)) ≫ E.counitIso.hom.app (H.obj X) =
    E.counitIso.hom.app X ≫ δ.app X at hNat
  calc
    _ = E.counitIso.inv.app X ≫ (E.counitIso.hom.app X ≫ δ.app X) :=
      congrArg (fun q => E.counitIso.inv.app X ≫ q) hNat
    _ = (E.counitIso.inv.app X ≫ E.counitIso.hom.app X) ≫ δ.app X :=
      (Category.assoc _ _ _).symm
    _ = δ.app X := by rw [Iso.inv_hom_id_app, Category.id_comp]

/-- Equal whole original coaugmentation and output initializers preserve that source transfer. -/
theorem carryCoaugmentation_output_of_initializers (η : 𝟭 C ⟶ R)
    (e : E.inverse ⋙ R ≅ H ⋙ E.inverse) (δ : 𝟭 D ⟶ H)
    (a : 𝟭 D ⟶ E.inverse ⋙ R ⋙ E.functor)
    (ha : a = carryCoaugmentation E R η)
    (b : E.inverse ⋙ R ⋙ E.functor ≅ H)
    (hb : b = carryOutputNatIso E R H e)
    (hSource : ∀ X : D,
      η.app (E.inverse.obj X) ≫ e.hom.app X = E.inverse.map (δ.app X)) :
    a ≫ b.hom = δ := by
  cases ha
  cases hb
  exact carryCoaugmentation_output_of_source E R H η e δ hSource

/-- The whole original whiskered source equation transfers through both actual equivalence maps. -/
theorem carryCoaugmentation_output_of_whiskered_source (η : 𝟭 C ⟶ R)
    (e : E.inverse ⋙ R ≅ H ⋙ E.inverse) (δ : 𝟭 D ⟶ H)
    (a : 𝟭 D ⟶ E.inverse ⋙ R ⋙ E.functor)
    (ha : a = carryCoaugmentation E R η)
    (b : E.inverse ⋙ R ⋙ E.functor ≅ H)
    (hb : b = carryOutputNatIso E R H e)
    (hSource : ∀ X : D,
      (Functor.whiskerLeft E.inverse η ≫ e.hom).app X = E.inverse.map (δ.app X)) :
    a ≫ b.hom = δ := by
  apply carryCoaugmentation_output_of_initializers E R H η e δ a ha b hb
  intro X
  exact hSource X

/-- Equality of the whole original inverse functor precedes every source-output component. -/
theorem carryCoaugmentation_output_of_inverse_functor
    (P : D ⥤ C) (hP : P = E.inverse) (η : 𝟭 C ⟶ R)
    (e : P ⋙ R ≅ H ⋙ P) (δ : 𝟭 D ⟶ H)
    (a : 𝟭 D ⟶ P ⋙ R ⋙ E.functor)
    (ha : HEq a (carryCoaugmentation E R η))
    (b : P ⋙ R ⋙ E.functor ≅ H)
    (hb : HEq b (carryOutputNatIso E R H (eqToIso
      (congrArg (fun Q => Q ⋙ R) hP).symm ≪≫ e ≪≫
        eqToIso (congrArg (fun Q => H ⋙ Q) hP))))
    (hSource : ∀ X : D,
      (Functor.whiskerLeft P η ≫ e.hom).app X = P.map (δ.app X)) :
    a ≫ b.hom = δ := by
  cases hP
  have ha' : a = carryCoaugmentation E R η := eq_of_heq ha
  have hb' : b = carryOutputNatIso E R H e := by
    simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl] using eq_of_heq hb
  exact carryCoaugmentation_output_of_whiskered_source E R H η e δ a ha' b hb' hSource

/-- The equality of whole original source transformations transfers through the original E. -/
theorem carryCoaugmentation_output_of_source_transformation (η : 𝟭 C ⟶ R)
    (e : E.inverse ⋙ R ≅ H ⋙ E.inverse) (δ : 𝟭 D ⟶ H)
    (hSource : Functor.whiskerLeft E.inverse η ≫ e.hom = Functor.whiskerRight δ E.inverse) :
    carryCoaugmentation E R η ≫ (carryOutputNatIso E R H e).hom = δ := by
  apply carryCoaugmentation_output_of_source E R H η e δ
  intro X
  exact congrArg (fun τ => τ.app X) hSource

/-- Both entire source-precomposition maps are carried through the original equivalence. -/
def carrySourceNatIso {R R' : C ⥤ C} (e : R ≅ R') :
    E.inverse ⋙ R ⋙ E.functor ≅ E.inverse ⋙ R' ⋙ E.functor :=
  Functor.isoWhiskerLeft E.inverse (Functor.isoWhiskerRight e E.functor)

/-- Source precomposition and target output comparison compose as whole original functors. -/
def carryFreeOutputNatIso {R R' : C ⥤ C} (e : R ≅ R')
    (h : E.inverse ⋙ R' ⋙ E.functor ≅ H) : E.inverse ⋙ R ⋙ E.functor ≅ H :=
  carrySourceNatIso E e ≪≫ h

/-- The original coaugmentation is transported by the complete inverse free-source comparison. -/
def changeSourceCoaugmentation {R R' : C ⥤ C} (e : R ≅ R')
    (η : 𝟭 D ⟶ E.inverse ⋙ R' ⋙ E.functor) :
    𝟭 D ⟶ E.inverse ⋙ R ⋙ E.functor :=
  η ≫ (carrySourceNatIso E e).inv

/-- Original source precomposition and its inverse cancel before the complete output comparison. -/
theorem changeSourceCoaugmentation_comp {R R' : C ⥤ C} (e : R ≅ R')
    (h : E.inverse ⋙ R' ⋙ E.functor ≅ H)
    (η : 𝟭 D ⟶ E.inverse ⋙ R' ⋙ E.functor) :
    changeSourceCoaugmentation E e η ≫ (carryFreeOutputNatIso E H e h).hom =
      η ≫ h.hom := by
  change (η ≫ (carrySourceNatIso E e).inv) ≫
    ((carrySourceNatIso E e).hom ≫ h.hom) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]

end Carrier

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.Internal

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-- The original morphisms of the orthogonal operator category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original direct-sum tensor on the orthogonal operator category. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed enrichment on the orthogonal operator category. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block-swap symmetry on the orthogonal operator category. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
/-- The original selected Day tensor on the orthogonal indexed spaces. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The original block-swap symmetry for the selected orthogonal Day tensor. -/
local instance : SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.symmetricCategory.{u, v}
/-- The original representation-sphere monoid for these source modules. -/
local instance : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
/-- The original commutativity proof of the representation-sphere monoid. -/
local instance : IsCommMonObj sphereISpace.{u, v} := OrthogonalDay.sphereIsCommMonObj.{u, v}
/-- The original pointed small limits used by the source mapping construction. -/
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}
/-- The selected closed Day structure on the original orthogonal indexed spaces. -/
local instance : MonoidalClosed (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  EnrichedDayKernel.Closed.monoidalClosed OrthogonalIndex.enrichedMonoidalData.{u, v}

open CanonicalSourceRightModuleActions CanonicalSourceRightModuleEquivalence

/-- The entire original native stock category is the same full generic source module category. -/
theorem nativeModuleCategory_eq_source :
    (inferInstance : Category SourceModule.{u, v}) =
      SphereModuleMappingEnd.moduleCategory OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} := by
  rfl

attribute [local instance] Enriched.prodCategory
  EnrichedDayKernel.ColimitMonoidal.smallestColimits
  SphereModuleMappingEnd.moduleCategory
  MonoidalLeftAction.monoidalOppositeLeftAction

open CanonicalSourceRightModuleActions CanonicalSourceRightModuleEquivalence
open FunctionSpectrum EnrichedDayKernel ModuleMappingR

private abbrev d := OrthogonalIndex.enrichedMonoidalData.{u, v}
private abbrev b := OrthogonalIndex.enrichedSymmetricData.{u, v}
private abbrev S := orthogonalSphereFunctor.{u, v}
private abbrev L := orthogonalSphereMonoidalData.{u, v}
private abbrev B := orthogonalSphereBraidedData.{u, v}

/-- The existing exact Mapping_R functor, with its original complete right-module arrows. -/
abbrev sourceFunction (M : SourceModule.{u, v}) : SourceModule.{u, v} ⥤ SourceModule.{u, v} :=
  ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} M

/-- The actual free right-sphere source, retaining the original I-space free generator. -/
abbrev sourceFree (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) : SourceModule.{u, v} :=
  FreeSource.freeAt r X

/-- The full actual native carrier used throughout the function-spectrum comparison. -/
abbrev Carrier := IterationMaps.Carrier.{u, v}

/-- The original source function-spectrum functor is restricted and reconstructed by the same E. -/
def mappingFunctor (A : Carrier.{u, v}) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  toModuleFunctor ⋙ sourceFunction (toModuleFunctor.obj A) ⋙ fromModuleFunctor

/-- This is precisely the chosen canonical source function spectrum, with the same whole E. -/
theorem mappingFunctor_eq_original (A : Carrier.{u, v}) :
    mappingFunctor A = CanonicalSourceSmashClosed.mappingFunctor A := rfl

/-- The complete original shifted scalar cotensor, including the continuous coend action. -/
abbrev shiftedCotensor (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    Carrier.{u, v} ⥤ Carrier.{u, v} :=
  RightShift.shift r ⋙ cotensor X

/-- The source NatIso retains the actual proved stock carrier and action comparisons. -/
def moduleOutputNatIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) :=
  Internal.freeOutputNatIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    r X toModuleFunctor (shiftedCotensor r X)
    (fun F => Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (FreeSourceAction.LiteralModuleStage.moduleIso r X F))
    (FreeSourceAction.LiteralModuleStage.target_objects r X)
    (by
      intro F c
      exact Internal.outputIso_component d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        r X (toModule F) (toModule (FreeSourceAction.NativeModule.shiftedCotensor r X F))
        (FreeSourceAction.LiteralModuleStage.carrierIso r X F)
        (FreeSourceAction.LiteralModuleStage.target_objects r X F)
        (FreeSourceAction.LiteralModuleStage.carrier_component r X F)
        (FreeSourceAction.LiteralModuleStage.target_action r X F) c)
    (by
      intro F G f c
      have h₁ := toModuleMap_component ((shiftedCotensor r X).map f) c
      have h₂ := cotensorMap_component X ((RightShift.shift r).map f)
        (OrthogonalOperatorIndex.ofIndex.{u, v} c)
      have h₃ := congrArg (ihom X).map (RightShift.shift_map_component r c f)
      have h₄ := congrArg (ihom X).map (toModuleMap_component f (c + r))
      exact (Category.comp_id _).trans
        ((h₁.trans (h₂.trans (h₃.trans h₄.symm))).trans (Category.id_comp _).symm))

/-- The entire native NatIso retains the same actual original factory, not a selected component. -/
theorem moduleOutputNatIso_factory_heq (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    HEq (moduleOutputNatIso r X)
      (Internal.freeOutputNatIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    r X toModuleFunctor (shiftedCotensor r X)
    (fun F => Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (FreeSourceAction.LiteralModuleStage.moduleIso r X F))
    (FreeSourceAction.LiteralModuleStage.target_objects r X)
    (by
      intro F c
      exact Internal.outputIso_component d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        r X (toModule F) (toModule (FreeSourceAction.NativeModule.shiftedCotensor r X F))
        (FreeSourceAction.LiteralModuleStage.carrierIso r X F)
        (FreeSourceAction.LiteralModuleStage.target_objects r X F)
        (FreeSourceAction.LiteralModuleStage.carrier_component r X F)
        (FreeSourceAction.LiteralModuleStage.target_action r X F) c)
    (by
      intro F G f c
      have h₁ := toModuleMap_component ((shiftedCotensor r X).map f) c
      have h₂ := cotensorMap_component X ((RightShift.shift r).map f)
        (OrthogonalOperatorIndex.ofIndex.{u, v} c)
      have h₃ := congrArg (ihom X).map (RightShift.shift_map_component r c f)
      have h₄ := congrArg (ihom X).map (toModuleMap_component f (c + r))
      exact (Category.comp_id _).trans
        ((h₁.trans (h₂.trans (h₃.trans h₄.symm))).trans (Category.id_comp _).symm))) := by
  rfl

/-- Every complete native component is retained by transport through the original whole factory. -/
theorem moduleOutputNatIso_hom_app_heq (r : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (F : Carrier.{u, v}) :
    HEq ((moduleOutputNatIso r X).hom.app F)
      (Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        (FreeSourceAction.LiteralModuleStage.moduleIso r X F)).hom := by
  exact
  Internal.freeOutputNatIso_component_of_whole_factory d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    r X toModuleFunctor (shiftedCotensor r X)
    (fun F => Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (FreeSourceAction.LiteralModuleStage.moduleIso r X F))
    (FreeSourceAction.LiteralModuleStage.target_objects r X)
    (by
      intro F c
      exact Internal.outputIso_component d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        r X (toModule F) (toModule (FreeSourceAction.NativeModule.shiftedCotensor r X F))
        (FreeSourceAction.LiteralModuleStage.carrierIso r X F)
        (FreeSourceAction.LiteralModuleStage.target_objects r X F)
        (FreeSourceAction.LiteralModuleStage.carrier_component r X F)
        (FreeSourceAction.LiteralModuleStage.target_action r X F) c)
    (by
      intro F G f c
      have h₁ := toModuleMap_component ((shiftedCotensor r X).map f) c
      have h₂ := cotensorMap_component X ((RightShift.shift r).map f)
        (OrthogonalOperatorIndex.ofIndex.{u, v} c)
      have h₃ := congrArg (ihom X).map (RightShift.shift_map_component r c f)
      have h₄ := congrArg (ihom X).map (toModuleMap_component f (c + r))
      exact (Category.comp_id _).trans
        ((h₁.trans (h₂.trans (h₃.trans h₄.symm))).trans (Category.id_comp _).symm))
    (inferInstance : Category SourceModule.{u, v}) nativeModuleCategory_eq_source
    (toModuleFunctor ⋙ sourceFunction (sourceFree r X))
    (shiftedCotensor r X ⋙ toModuleFunctor)
    (HEq.refl _) (HEq.refl _)
    (moduleOutputNatIso r X) (moduleOutputNatIso_factory_heq r X) F


/-- The exact original free-source function comparison is a complete native natural isomorphism. -/
def sourceFreeOutputNatIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) :=
  Internal.carryOutputNatIso equivalence.symm (sourceFunction (sourceFree r X))
    (shiftedCotensor r X) (moduleOutputNatIso r X)

/-- The actual native enriched free spectrum, with its complete original operator action. -/
abbrev nativeFree (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) : Carrier.{u, v} :=
  EnrichedFunctorCat.Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) X

/-- Both original free/evaluation maps act contravariantly on the complete function module. -/
def freeSourceNatIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) :=
  Internal.sourceNatIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    (FreeSourceAction.OriginalOperator.Family.sourceFreeIso d.{u, v} S.{u, v} L.{u, v}
      equivalence.symm CanonicalSourceRightModuleFreeEvaluation.evaluationComparison r X)

/-- The same full original native free-source function functor is naturally the shifted cotensor. -/
def nativeFreeFunctionNatIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) :=
  Internal.carryFreeOutputNatIso equivalence.symm (shiftedCotensor r X)
    (freeSourceNatIso r X) (sourceFreeOutputNatIso r X)

/-- The complete function spectrum from the original first representation sphere. -/
abbrev stabilizationFunction : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  mappingFunctor (nativeFree 1 (PointedCGWH.orthogonalSphere.{u, v} 1))

/-- Both complete original free-function maps and the original sphere-one comparison identify R. -/
def stabilizationFunctionIso : stabilizationFunction.{u, v} ≅
    Delooping.firstDeloopingLoop.{u, v} :=
  nativeFreeFunctionNatIso 1 (PointedCGWH.orthogonalSphere.{u, v} 1) ≪≫
    Functor.isoWhiskerLeft Delooping.firstDelooping Delooping.firstLoopIso

/-- The genuine first function spectrum uses the actual original public scalar-loop functor. -/
def stabilizationFunctionScalarIso : stabilizationFunction.{u, v} ≅
    Delooping.firstDelooping ⋙ NegativeHomTests.scalarLoopFunctor :=
  stabilizationFunctionIso ≪≫
    eqToIso (congrArg (fun H : Carrier.{u, v} ⥤ Carrier.{u, v} =>
      Delooping.firstDelooping ⋙ H) NegativeHomTests.scalarLoopFunctor_eq_cotensor.symm)

/-- The original regular-sphere module in the same Mapping_R source convention. -/
abbrev regularModule : SourceModule.{u, v} :=
  FreeSourceAction.NativeCanonicalDelta.regularModule.{u, v}

/-- Both original full regular evaluation maps are natural at every module target. -/
def regularEvaluationNatIso : sourceFunction regularModule.{u, v} ≅ 𝟭 SourceModule.{u, v} :=
  RightModuleMappingEnd.Regular.regularMappingNatIso sphereISpace.{u, v}

/-- The actual source free-sphere map, with the original degree pair and coefficient. -/
abbrev sourceSphereMap : sourceFree.{u, v} 1 (PointedCGWH.orthogonalSphere 1) ⟶
    regularModule := FreeSourceAction.NativeCanonicalDelta.sphereMap 1

/-- Original lambda-star is genuine regular evaluation followed by original source precomposition. -/
def sourceLambdaStar : 𝟭 SourceModule.{u, v} ⟶
    sourceFunction (sourceFree 1 (PointedCGWH.orthogonalSphere 1)) :=
  Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} 1

/-- The same original source precomposition is carried through both actual native equivalence maps. -/
def nativeSourceLambdaStar : 𝟭 Carrier.{u, v} ⟶
    toModuleFunctor ⋙ sourceFunction (sourceFree 1 (PointedCGWH.orthogonalSphere 1)) ⋙
      fromModuleFunctor :=
  unitIso.hom ≫
    Functor.whiskerLeft toModuleFunctor (Functor.whiskerRight sourceLambdaStar fromModuleFunctor)

/-- The original lambda-star with its actual native free source and both source-comparison maps. -/
def lambdaStar.{u_1, u_2} :
    𝟭 Carrier.{u_2, u_1} ⟶ stabilizationFunction.{u_2, u_1} :=
  Internal.changeSourceCoaugmentation equivalence.symm
    (freeSourceNatIso 1 (PointedCGWH.orthogonalSphere 1)) nativeSourceLambdaStar

/-- Every complete original spectrum arrow is retained by the native lambda-star square. -/
theorem lambdaStar_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    f ≫ lambdaStar.app Y = lambdaStar.app X ≫ stabilizationFunction.map f :=
  lambdaStar.naturality f

/-- The full actual free-source comparison cancels the same original source precomposition Iso. -/
theorem lambdaStar_freeOutput :
    lambdaStar.{u, v} ≫
        (nativeFreeFunctionNatIso 1 (PointedCGWH.orthogonalSphere 1)).hom =
      nativeSourceLambdaStar ≫
        (sourceFreeOutputNatIso 1 (PointedCGWH.orthogonalSphere 1)).hom :=
  Internal.changeSourceCoaugmentation_comp equivalence.symm
    (shiftedCotensor 1 (PointedCGWH.orthogonalSphere 1))
    (freeSourceNatIso 1 (PointedCGWH.orthogonalSphere 1))
    (sourceFreeOutputNatIso 1 (PointedCGWH.orthogonalSphere 1)) nativeSourceLambdaStar

/-- The actual native source module Iso is the complete original generic output factory. -/
theorem moduleIso_factory_heq (r : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (F : Carrier.{u, v}) :
    HEq (FreeSourceAction.LiteralModuleStage.moduleIso r X F)
      (FreeSourceAction.Mapping.SourceStage.outputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        r X (toModule F) (toModule (FreeSourceAction.NativeModule.shiftedCotensor r X F))
        (FreeSourceAction.LiteralModuleStage.carrierIso r X F)
        (FreeSourceAction.LiteralModuleStage.target_objects r X F)
        (FreeSourceAction.LiteralModuleStage.carrier_component r X F)
        (FreeSourceAction.LiteralModuleStage.target_action r X F)) := by
  rfl

/-- The native output component keeps the generic source module before its object is evaluated. -/
theorem moduleOutputNatIso_hom_app_generic_heq
    (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : Carrier.{u, v}) :
    HEq ((moduleOutputNatIso r X).hom.app F)
      (Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        (M := CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r X)
        (FreeSourceAction.Mapping.SourceStage.outputIso
          d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
          r X (toModule F) (toModule (FreeSourceAction.NativeModule.shiftedCotensor r X F))
          (FreeSourceAction.LiteralModuleStage.carrierIso r X F)
          (FreeSourceAction.LiteralModuleStage.target_objects r X F)
          (FreeSourceAction.LiteralModuleStage.carrier_component r X F)
          (FreeSourceAction.LiteralModuleStage.target_action r X F))).hom := by
  have h := Internal.functorOutputIso_hom_of_whole_source
    d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    (M' := CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r X)
    rfl rfl rfl (FreeSourceAction.LiteralModuleStage.moduleIso r X F) _
    (moduleIso_factory_heq r X F)
  exact (moduleOutputNatIso_hom_app_heq r X F).trans h

/-- The whole source coaugmentation followed by the original free output is native source delta. -/
theorem sourceLambda_output_native (r : OrthogonalIndex) (F : Carrier.{u, v}) :
    HEq
      ((Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r).app (toModule F) ≫
        (Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
          (FreeSourceAction.LiteralModuleStage.moduleIso r (S.{u, v}.obj r) F)).hom)
      (FreeSourceAction.LiteralModuleStage.sourceComparison r F) := by
  have he := moduleIso_factory_heq r (S.{u, v}.obj r) F
  have hRead := Internal.functorOutputIso_heq d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    (FreeSourceAction.LiteralModuleStage.moduleIso r (S.{u, v}.obj r) F) _ he
  exact Internal.sourceLambda_output_of_whole_factories
    d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    r (toModule F) (toModule (FreeSourceAction.NativeModule.shiftedCotensor r (S.{u, v}.obj r) F))
    (FreeSourceAction.LiteralModuleStage.carrierIso r (S.{u, v}.obj r) F)
    (FreeSourceAction.LiteralModuleStage.target_objects r (S.{u, v}.obj r) F)
    (FreeSourceAction.LiteralModuleStage.carrier_component r (S.{u, v}.obj r) F)
    (FreeSourceAction.LiteralModuleStage.target_action r (S.{u, v}.obj r) F)
    (inferInstance : Category SourceModule.{u, v}) nativeModuleCategory_eq_source
    (toModule F) (toModule (FreeSourceAction.NativeModule.shiftedCotensor r (S.{u, v}.obj r) F))
    (toModule F) (toModule ((Delooping.shiftedLoop r).obj F))
    rfl rfl rfl (congrArg toModule (FreeSourceAction.LiteralModuleStage.shiftedLoop_eq r F)).symm
    (sourceFunction (sourceFree r (S.{u, v}.obj r))) (HEq.refl _)
    (Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r) (HEq.refl _)
    (Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (FreeSourceAction.LiteralModuleStage.moduleIso r (S.{u, v}.obj r) F)) hRead
    (FreeSourceAction.LiteralModuleStage.sourceComparison r F)
    (FreeSourceAction.LiteralModuleStage.sourceComparison_factory_heq r F)

/-- The original restriction functor keeps its whole source object before evaluation. -/
theorem toModuleFunctor_obj_eq (F : Carrier.{u, v}) : toModuleFunctor.obj F = toModule F := rfl

/-- The actual whole composite with identity retains the original source object. -/
theorem sourceLambda_whisker_source_obj (F : Carrier.{u, v}) :
    (toModuleFunctor ⋙ 𝟭 SourceModule.{u, v}).obj F = (𝟭 SourceModule.{u, v}).obj (toModule F) :=
  CategoryTransport.compFunctorObjEq _ _ nativeModuleCategory_eq_source
    toModuleFunctor toModuleFunctor (𝟭 SourceModule.{u, v}) (𝟭 SourceModule.{u, v})
    (HEq.refl _) (HEq.refl _) F

/-- The actual complete Mapping_R composite retains the same original target object. -/
theorem sourceLambda_whisker_target_obj (r : OrthogonalIndex) (F : Carrier.{u, v}) :
    (toModuleFunctor ⋙ sourceFunction (sourceFree r (S.{u, v}.obj r))).obj F =
      (sourceFunction (sourceFree r (S.{u, v}.obj r))).obj (toModule F) :=
  CategoryTransport.compFunctorObjEq _ _ nativeModuleCategory_eq_source
    toModuleFunctor toModuleFunctor
    (ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r (S.{u, v}.obj r)))
    (ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r (S.{u, v}.obj r)))
    (HEq.refl _) (HEq.refl _) F

/-- The entire original whiskered source coaugmentation retains its actual target component. -/
theorem sourceLambda_whiskerLeft_app_heq (r : OrthogonalIndex) (F : Carrier.{u, v}) :
    HEq ((Functor.whiskerLeft toModuleFunctor
        (Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r)).app F)
      ((Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r).app
        (toModule F)) := by
  exact CategoryTransport.whiskerLeftAppHEq_of_objects toModuleFunctor
    (Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r)
    F (toModule F) (toModuleFunctor_obj_eq F)
    (sourceLambda_whisker_source_obj F) (sourceLambda_whisker_target_obj r F)

/-- The generic original output hom is the actual full native output hom under its original factory. -/
theorem moduleOutput_generic_to_native_heq (r : OrthogonalIndex)
    (X : PointedCGWH.{u, v}) (F : Carrier.{u, v}) :
    HEq (Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      (M := CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r X)
      (FreeSourceAction.Mapping.SourceStage.outputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        r X (toModule F) (toModule (FreeSourceAction.NativeModule.shiftedCotensor r X F))
        (FreeSourceAction.LiteralModuleStage.carrierIso r X F)
        (FreeSourceAction.LiteralModuleStage.target_objects r X F)
        (FreeSourceAction.LiteralModuleStage.carrier_component r X F)
        (FreeSourceAction.LiteralModuleStage.target_action r X F))).hom
      (Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        (FreeSourceAction.LiteralModuleStage.moduleIso r X F)).hom := by
  exact (Internal.functorOutputIso_hom_of_whole_source
    d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    (M' := CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r X)
    rfl rfl rfl (FreeSourceAction.LiteralModuleStage.moduleIso r X F) _
    (moduleIso_factory_heq r X F)).symm

/-- The complete original native module output equals its original generic source composition. -/
theorem sourceLambda_moduleOutput_generic_heq (r : OrthogonalIndex) (F : Carrier.{u, v}) : HEq
      ((Functor.whiskerLeft toModuleFunctor
          (Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r) ≫
        (moduleOutputNatIso r (S.{u, v}.obj r)).hom).app F)
      ((Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r).app
        (toModule F) ≫
        (Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
          (M := CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt
            d.{u, v} S.{u, v} L.{u, v} r (S.{u, v}.obj r))
          (FreeSourceAction.Mapping.SourceStage.outputIso
            d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
            r (S.{u, v}.obj r) (toModule F)
            (toModule (FreeSourceAction.NativeModule.shiftedCotensor r (S.{u, v}.obj r) F))
            (FreeSourceAction.LiteralModuleStage.carrierIso r (S.{u, v}.obj r) F)
            (FreeSourceAction.LiteralModuleStage.target_objects r (S.{u, v}.obj r) F)
            (FreeSourceAction.LiteralModuleStage.carrier_component r (S.{u, v}.obj r) F)
            (FreeSourceAction.LiteralModuleStage.target_action r (S.{u, v}.obj r) F))).hom) := by
  have hRaw := moduleOutputNatIso_hom_app_generic_heq r (S.{u, v}.obj r) F
  apply heq_comp
  · rfl
  · exact CategoryTransport.compFunctorObjEq _ _ nativeModuleCategory_eq_source
      toModuleFunctor toModuleFunctor
      (ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r (S.{u, v}.obj r)))
      (ModuleMappingR.functor d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r (S.{u, v}.obj r)))
      (HEq.refl _) (HEq.refl _) F
  · rfl
  · exact sourceLambda_whiskerLeft_app_heq r F
  · exact hRaw

/-- At every source index the entire original module coaugmentation gives native source delta. -/
theorem sourceLambda_moduleOutput (r : OrthogonalIndex) (F : Carrier.{u, v}) :
    (Functor.whiskerLeft toModuleFunctor
        (Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r) ≫
      (moduleOutputNatIso r (S.{u, v}.obj r)).hom).app F =
        FreeSourceAction.LiteralModuleStage.sourceComparison r F := by
  have hComp := sourceLambda_moduleOutput_generic_heq r F
  have hHom := moduleOutput_generic_to_native_heq r (S.{u, v}.obj r) F
  have hNativeComp : HEq
      ((Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r).app
        (toModule F) ≫
        (Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
          (M := CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt
            d.{u, v} S.{u, v} L.{u, v} r (S.{u, v}.obj r))
          (FreeSourceAction.Mapping.SourceStage.outputIso
            d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
            r (S.{u, v}.obj r) (toModule F)
            (toModule (FreeSourceAction.NativeModule.shiftedCotensor r (S.{u, v}.obj r) F))
            (FreeSourceAction.LiteralModuleStage.carrierIso r (S.{u, v}.obj r) F)
            (FreeSourceAction.LiteralModuleStage.target_objects r (S.{u, v}.obj r) F)
            (FreeSourceAction.LiteralModuleStage.carrier_component r (S.{u, v}.obj r) F)
            (FreeSourceAction.LiteralModuleStage.target_action r (S.{u, v}.obj r) F))).hom)
      ((Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r).app
        (toModule F) ≫
        (Internal.functorOutputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
          (FreeSourceAction.LiteralModuleStage.moduleIso r (S.{u, v}.obj r) F)).hom) := by
    apply heq_comp
    · rfl
    · rfl
    · rfl
    · exact HEq.refl _
    · exact hHom
  exact eq_of_heq (hComp.trans (hNativeComp.trans (sourceLambda_output_native r F)))

/-- The full original E-conjugated source-output equation, before native map projection. -/
def NativeSourceLambdaOutputProperty : Prop :=
  nativeSourceLambdaStar.{u, v} ≫
    (sourceFreeOutputNatIso 1 (PointedCGWH.orthogonalSphere 1)).hom =
      Delooping.comparisonNat 1

/-- The whole original lambda source transformation is exactly its original internal initializer. -/
theorem sourceLambdaStar_initializer_eq :
    sourceLambdaStar.{u, v} =
      Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} 1 := rfl

/-- The whole original source module equation uses the full actual internal source transformation. -/
theorem sourceLambdaStar_output_source (F : Carrier.{u, v}) : type_of% (
    sourceLambda_moduleOutput 1 F) := sourceLambda_moduleOutput 1 F

/-- The same actual original source equation retains the complete Delooping restriction map. -/
theorem sourceLambdaStar_output_source_map (F : Carrier.{u, v}) : type_of% (
    (sourceLambdaStar_output_source F).trans
      (FreeSourceAction.LiteralModuleStage.sourceComparison_eq 1 F)) :=
  (sourceLambdaStar_output_source F).trans
    (FreeSourceAction.LiteralModuleStage.sourceComparison_eq 1 F)

/-- The actual whole original source map equality, before E is applied. -/
theorem sourceLambdaStar_output_source_nat : type_of% (
    (show Functor.whiskerLeft toModuleFunctor
      (Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} 1) ≫
        (moduleOutputNatIso 1 (PointedCGWH.orthogonalSphere 1)).hom =
      Functor.whiskerRight (Delooping.comparisonNat 1) toModuleFunctor from by
      apply NatTrans.ext
      funext F
      exact sourceLambdaStar_output_source_map F)) := by
  apply NatTrans.ext
  funext F
  exact sourceLambdaStar_output_source_map F

/-- The original native source coaugmentation is its complete unchanged E-carry initializer. -/
theorem nativeSourceLambdaStar_factory_heq :
    HEq nativeSourceLambdaStar.{u, v}
      (Internal.carryCoaugmentation equivalence.symm
        (sourceFunction (sourceFree 1 (PointedCGWH.orthogonalSphere 1)))
        (Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} 1)) := by
  rfl

/-- The whole original native output Iso is its complete unchanged E-carry initializer. -/
theorem sourceFreeOutputNatIso_factory_heq (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) :
    HEq (sourceFreeOutputNatIso r X)
      (Internal.carryOutputNatIso equivalence.symm (sourceFunction (sourceFree r X))
        (shiftedCotensor r X) (moduleOutputNatIso r X)) := by
  rfl

/-- Both original E factors identify the complete source-lambda output transformation. -/
theorem nativeSourceLambdaStar_output_nat : NativeSourceLambdaOutputProperty.{u, v} := by
  have h := Internal.carryCoaugmentation_output_of_source_transformation equivalence.symm
    (sourceFunction (sourceFree 1 (PointedCGWH.orthogonalSphere 1)))
    (shiftedCotensor 1 (PointedCGWH.orthogonalSphere 1))
    (Internal.sourceLambda d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} 1)
    (moduleOutputNatIso 1 (PointedCGWH.orthogonalSphere 1)) (Delooping.comparisonNat 1)
    sourceLambdaStar_output_source_nat
  exact h

/-- Every component of the same whole source output retains both original E maps. -/
theorem nativeSourceLambdaStar_output (F : Carrier.{u, v}) :
    (nativeSourceLambdaStar ≫
      (sourceFreeOutputNatIso 1 (PointedCGWH.orthogonalSphere 1)).hom).app F =
        Delooping.comparison 1 F :=
  congrArg (fun η => η.app F) nativeSourceLambdaStar_output_nat

/-- The entire original free-source function comparison carries lambda-star to native delta. -/
theorem lambdaStar_stabilizationFunctionIso :
    lambdaStar.{u, v} ≫ stabilizationFunctionIso.hom = Delooping.delta := by
  let e₀ : stabilizationFunction.{v, u} ≅
      shiftedCotensor.{v, u} 1 (PointedCGWH.orthogonalSphere.{v, u} 1) :=
    nativeFreeFunctionNatIso.{v, u} 1 (PointedCGWH.orthogonalSphere.{v, u} 1)
  let e₁ : shiftedCotensor.{v, u} 1 (PointedCGWH.orthogonalSphere.{v, u} 1) ≅
      Delooping.firstDeloopingLoop.{v, u} :=
    Functor.isoWhiskerLeft Delooping.firstDelooping.{v, u} Delooping.firstLoopIso.{v, u}
  have hIso : stabilizationFunctionIso.{v, u} = e₀ ≪≫ e₁ := rfl
  have h₀ : lambdaStar.{u, v} ≫ e₀.hom = Delooping.comparisonNat.{v, u} 1 :=
    lambdaStar_freeOutput.trans nativeSourceLambdaStar_output_nat
  calc
    lambdaStar.{u, v} ≫ stabilizationFunctionIso.{v, u}.hom =
        (lambdaStar.{u, v} ≫ e₀.hom) ≫ e₁.hom := by
      rw [hIso, Iso.trans_hom, Category.assoc]
    _ = Delooping.comparisonNat.{v, u} 1 ≫ e₁.hom :=
      congrArg (fun η => η ≫ e₁.hom) h₀
    _ = Delooping.delta.{v, u} := rfl

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration
