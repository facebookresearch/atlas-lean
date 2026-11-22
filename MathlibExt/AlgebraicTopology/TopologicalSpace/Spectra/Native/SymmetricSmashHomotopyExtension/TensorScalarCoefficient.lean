/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension.NativeTensorScalarFunctor
import MathlibExt.CategoryTheory.Monoidal.TensorRepresentedInterchange
import Batteries.Tactic.Lint

/-!
# Coefficient naturality of scalar tensor comparisons

Tensoring a symmetric spectrum with a degree-zero free coefficient
spectrum is naturally isomorphic to scalar tensoring of enriched spectra.
The component isomorphisms respect every pointed coefficient map.
The scalar-smash interchange comparison is likewise natural in the
coefficient while its two spectrum arguments are arbitrary.
-/

set_option autoImplicit false
noncomputable section
universe u v uP vP uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.CoefficientPrimitive

private theorem isoComp_congr {C : Type uD} [Category.{vD} C] {X Y Z : C}
    {e e' : X ≅ Y} {f f' : Y ≅ Z} (he : e = e') (hf : f = f') :
    e ≪≫ f = e' ≪≫ f' := by
  cases he
  cases hf
  rfl

private theorem isoFamilyComp_app {P : Type uP} [Category.{vP} P]
    {D : Type uD} [Category.{vD} D] {F G H : P ⥤ D}
    (e : F ≅ G) (f : G ≅ H) (X : P)
    {e' : F.obj X ≅ G.obj X} {f' : G.obj X ≅ H.obj X}
    (he : e.app X = e') (hf : f.app X = f') :
    (e ≪≫ f).app X = e' ≪≫ f' := by
  change e.app X ≪≫ f.app X = e' ≪≫ f'
  exact isoComp_congr he hf

private theorem sourceEqIso_app {P : Type uP} [Category.{vP} P]
    {D : Type uD} [Category.{vD} D] {F G : P ⥤ D} (h : F = G) (X : P) :
    (eqToIso h).app X = eqToIso (Functor.congr_obj h X) := by
  cases h
  rfl

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash.CoefficientPrimitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}

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
  SymmetricSmash.monoidalCategory SymmetricSmash.symmetricCategory SymmetricSmash.monoidalClosed

attribute [local irreducible] NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor

private theorem tensorScalarInitializer (T : V.{u, v}) :
    eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash (zeroFree T)) ≪≫
      originalSmashScalarIso T = tensorScalarIso T := rfl

attribute [local irreducible] originalSmashScalarIso tensorScalarIso

private theorem entireTensorSource :
    ScalarLeftBoundary.zeroFreeCoefficientFunctor ⋙ MonoidalCategory.curriedTensor Carrier.{u, v} =
      ScalarLeftBoundary.nativeScalarLeft.{u, v} :=
  (congrArg (fun F : Carrier.{u, v} ⥤ Carrier.{u, v} ⥤ Carrier.{u, v} =>
    ScalarLeftBoundary.zeroFreeCoefficientFunctor ⋙ F) nativeTensorBifunctor_eq_boundary).trans
      ScalarLeftBoundary.nativeScalarLeft_whole.symm

/-- The complete actual tensor/scalar comparison is natural in the original pointed coefficient. -/
def actualTensorScalarComparison :
    ScalarLeftBoundary.zeroFreeCoefficientFunctor ⋙ MonoidalCategory.curriedTensor Carrier.{u, v} ≅
      ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  eqToIso entireTensorSource ≪≫ ScalarLeftBoundary.actualScalarLeftComparison

/-- The complete tensor source equality keeps every unchanged tensorScalarIso initializer. -/
theorem actualTensorScalarComparison_app (T : V.{u, v}) :
    actualTensorScalarComparison.app T = tensorScalarIso T := by
  have hc : (eqToIso entireTensorSource).app T =
      eqToIso (SymmetricSmash.tensorLeft_eq_originalSmash (zeroFree T)) :=
    (CoefficientPrimitive.sourceEqIso_app entireTensorSource T).trans
      (congrArg eqToIso (Subsingleton.elim _ _))
  exact (CoefficientPrimitive.isoFamilyComp_app (eqToIso entireTensorSource)
    ScalarLeftBoundary.actualScalarLeftComparison T hc
    (ScalarLeftBoundary.actualScalarLeftComparison_app T)).trans (tensorScalarInitializer T)

/-- Every original coefficient arrow preserves the entire actual tensor/scalar comparison. -/
theorem tensorScalarIso_coefficient {T T' : V.{u, v}} (p : T ⟶ T') :
    (MonoidalCategory.curriedTensor Carrier.{u, v}).map
        (ScalarLeftBoundary.zeroFreeCoefficientFunctor.map p) ≫ (tensorScalarIso T').hom =
      (tensorScalarIso T).hom ≫
        (ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p := by
  have h := actualTensorScalarComparison.hom.naturality p
  change (MonoidalCategory.curriedTensor Carrier.{u, v}).map
      (ScalarLeftBoundary.zeroFreeCoefficientFunctor.map p) ≫ (actualTensorScalarComparison.app T').hom =
    (actualTensorScalarComparison.app T).hom ≫
      (ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p at h
  have hT := congrArg (fun e => e.hom) (actualTensorScalarComparison_app T)
  have hT' := congrArg (fun e => e.hom) (actualTensorScalarComparison_app T')
  have hL := congrArg (fun e => (MonoidalCategory.curriedTensor Carrier.{u, v}).map
    (ScalarLeftBoundary.zeroFreeCoefficientFunctor.map p) ≫ e) hT'
  have hR := congrArg (fun e => e ≫
    (ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p) hT
  exact hL.symm.trans (h.trans hR)

/-- The literal original native coefficient tensor map preserves every original component. -/
theorem tensorScalarIso_coefficient_app {T T' : V.{u, v}} (p : T ⟶ T') (X : Carrier.{u, v}) :
    (ScalarLeftBoundary.zeroFreeCoefficientFunctor.map p ▷ X) ≫ (tensorScalarIso T').hom.app X =
      (tensorScalarIso T).hom.app X ≫
        ((ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p).app X :=
  congrArg (fun f => f.app X) (tensorScalarIso_coefficient p)

/-- Every original coefficient arrow preserves scalar smash on both arbitrary original spectra. -/
theorem scalarSmashIso_coefficient {T T' : V.{u, v}} (p : T ⟶ T') (X Y : Carrier.{u, v}) :
    ((ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p).app (X ⊗ Y) ≫
      (scalarSmashIso T' X Y).hom =
    (scalarSmashIso T X Y).hom ≫
      (((ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p).app X ▷ Y) :=
  CategoryTheory.TensorRepresentedInterchange.coefficient_naturality
    (ScalarLeftBoundary.zeroFreeCoefficientFunctor.map p)
    ((ScalarLeibniz.tensorBifunctor (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map p)
    (tensorScalarIso T) (tensorScalarIso T') (tensorScalarIso_coefficient_app p) X Y








end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricScalarSmash

#lint only unusedArguments in
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricSmashHomotopyExtension
#lint only unusedArguments
