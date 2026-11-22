/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.FunctionScalarCoefficient
import MathlibExt.CategoryTheory.Adjunction.ParametrizedLeftIsoComparison
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Scalar cotensors from symmetric free-source internal Hom

Restriction of the symmetric function-spectrum bifunctor to free objects at the
tensor-unit index is compared naturally with scalar cotensoring. The comparison retains
contravariant coefficient maps, free-source precomposition and the given function-scalar
isomorphism at each coefficient.
-/

set_option autoImplicit false
noncomputable section

universe u v uC vC uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.CoefficientPrimitive

universe uEtaC vEtaC uEtaD vEtaD

private theorem functor_eta {C : Type uEtaC} [Category.{vEtaC} C]
    {D : Type uEtaD} [Category.{vEtaD} D] (F : C ⥤ D) :
    ({ obj := F.obj, map := F.map, map_id := F.map_id, map_comp := F.map_comp } : C ⥤ D) =
      F := rfl

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.CoefficientPrimitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev E := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric

private theorem nativeWholeRight :
    Mod.EquivalenceFunctionTransport.bifunctor A.{u, v} E.{u, v} =
      NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v} := rfl

private def zeroFreeFunctor : V.{u, v} ⥤ Carrier.{u, v} where
  obj := zeroFree
  map := Free.coefficientMap (PointedCGWH.symmetricOperatorObj (𝟙_ I))
  map_id := (Free.functor (PointedCGWH.symmetricOperatorObj (𝟙_ I))).map_id
  map_comp := (Free.functor (PointedCGWH.symmetricOperatorObj (𝟙_ I))).map_comp

private theorem zeroFreeFunctor_whole :
    zeroFreeFunctor.{u, v} = Free.functor (PointedCGWH.symmetricOperatorObj (𝟙_ I)) := rfl

private def nativeRightBifunctor : Carrier.{u, v}ᵒᵖ ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} where
  obj := fun X => NativeOmegaPreparation.NativeSymmetricFunction.functor X.unop
  map := fun p => NativeOmegaPreparation.NativeSymmetricFunction.precompose p.unop
  map_id := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.map_id
  map_comp := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.map_comp

private theorem nativeRightBifunctor_whole :
    nativeRightBifunctor.{u, v} =
      NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v} := by
  have h : nativeRightBifunctor.{u, v} =
      { obj := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.obj
        map := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.map
        map_id := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.map_id
        map_comp := NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.map_comp } := rfl
  exact h.trans (CoefficientPrimitive.functor_eta _)

private theorem nativeWholeSmashGetter :
    Mod.EquivalenceFunctionTransport.smashFunctor A.{u, v} E.{u, v} =
      NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor.{u, v} := rfl

attribute [local irreducible] zeroFree NativeOmegaPreparation.NativeSymmetricFunction.functor
  NativeOmegaPreparation.NativeSymmetricFunction.precompose
  NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor

private def nativeScalarRight : V.{u, v}ᵒᵖ ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} where
  obj := fun T => NativeOmegaPreparation.NativeSymmetricFunction.functor (zeroFree T.unop)
  map := fun p => NativeOmegaPreparation.NativeSymmetricFunction.precompose
    (zeroFreeFunctor.map p.unop)
  map_id := (zeroFreeFunctor.op ⋙ nativeRightBifunctor).map_id
  map_comp := (zeroFreeFunctor.op ⋙ nativeRightBifunctor).map_comp

private theorem nativeScalarRight_whole :
    nativeScalarRight.{u, v} = zeroFreeFunctor.op ⋙
      NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v} := by
  rw [← nativeRightBifunctor_whole]
  rfl

attribute [local semireducible] zeroFree

set_option maxHeartbeats 500000 in
-- Keep the exact previously diagnosed right component constructor finite.
private def scalarRightComparison :
    nativeScalarRight.{u, v} ≅
      ScalarLeibniz.cotensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  NatIso.ofComponents (fun T => functionScalarIso T.unop) (by
    intro T T' p
    exact functionScalarIso_coefficient p.unop)

private theorem scalarRightComparison_app (T : V.{u, v}ᵒᵖ) :
    scalarRightComparison.app T = functionScalarIso T.unop := rfl










/-- The full original native function bifunctor along the real zero-free coefficient functor. -/
def nativeScalarRightBoundary : V.{u, v}ᵒᵖ ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} :=
  nativeScalarRight

/-- The whole constructor is the unchanged actual native bifunctor on the original free family. -/
theorem nativeScalarRightBoundary_whole :
    nativeScalarRightBoundary.{u, v} =
      (Free.functor (PointedCGWH.symmetricOperatorObj (𝟙_ I))).op ⋙
        NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v} :=
  nativeScalarRight_whole.trans
    (congrArg (fun K : V.{u, v} ⥤ Carrier.{u, v} =>
      K.op ⋙ NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v}) zeroFreeFunctor_whole)

/-- All original scalar pre-maps, typed over the complete actual right bifunctor. -/
def originalScalarRightMapFamily :
    ∀ {T T' : V.{u, v}ᵒᵖ}, (T ⟶ T') →
      (nativeScalarRightBoundary.obj T ⟶ nativeScalarRightBoundary.obj T') :=
  @CategoryTheory.Functor.map _ _ _ _ (zeroFreeFunctor.op ⋙ nativeRightBifunctor)

/-- The typed family retains every literal original native free-source pre-map before coefficients. -/
theorem originalScalarRightMapFamily_whole :
    HEq (@originalScalarRightMapFamily.{u, v})
      (fun {T T' : V.{u, v}ᵒᵖ} (p : T ⟶ T') =>
        NativeOmegaPreparation.NativeSymmetricFunction.precompose
          (Free.coefficientMap (PointedCGWH.symmetricOperatorObj (𝟙_ I)) p.unop)) :=
  HEq.refl _

/-- Every entire coefficient map remains the original native free-source pre-map. -/
theorem nativeScalarRightBoundary_map {T T' : V.{u, v}ᵒᵖ} (p : T ⟶ T') :
    nativeScalarRightBoundary.map p = originalScalarRightMapFamily p := rfl

/-- The full original zero-free function/scalar comparison is natural in its actual coefficient. -/
def actualFunctionScalarComparison :
    nativeScalarRightBoundary.{u, v} ≅
      ScalarLeibniz.cotensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  scalarRightComparison

/-- Every component remains the exact original functionScalarIso initializer. -/
theorem actualFunctionScalarComparison_app (T : V.{u, v}ᵒᵖ) :
    actualFunctionScalarComparison.app T = functionScalarIso T.unop := rfl







end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash
