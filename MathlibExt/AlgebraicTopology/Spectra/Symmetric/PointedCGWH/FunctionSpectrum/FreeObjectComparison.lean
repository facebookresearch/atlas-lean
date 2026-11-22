/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.FreeModuleComparison

/-!
# Complete original symmetric free-function object comparison

The original module comparison is carried through the original whole module/operator
functor and its carrier counit. Both original component maps and all enriched Hom
naturality equations are retained on the genuine native carrier.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj
namespace NativeOmegaRecovery.NativeSymmetricFreeFunction
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
open PointedCGWH.SymmetricModulePresentation
attribute [local instance] PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

/-- The complete actual module/operator comparison retains the original carrier counit. -/
def objectIso (r : I) (M : V.{u, v}) (N : OriginalModule.{u, v}) :
    toOperatorFunctor (originalHom r M N) ≅ target r M N :=
  moduleToOperator.{u, v}.mapIso (moduleIso r M N) ≪≫ operatorRecoveryIso (target r M N)

private theorem mapIso_counit_hom_component (H : OriginalModule.{u, v})
    (F : NativeCarrier.{u, v}) (e : H ≅ reconstructedModule F) (n : I) :
    component (moduleToOperator.{u, v}.mapIso e ≪≫ operatorRecoveryIso F).hom
        (PointedCGWH.symmetricOperatorObj.{u, v} n) = e.hom.hom.natTrans.app n := by
  let K := reconstructedModule F
  let f : H ⟶ K := e.hom
  have h := toOperatorMorphism_component f (PointedCGWH.symmetricOperatorObj.{u, v} n)
  have hc := operatorRecoveryIso_hom_component F (PointedCGWH.symmetricOperatorObj.{u, v} n)
  change component (toOperatorMorphism f ≫ (operatorRecoveryIso F).hom)
    (PointedCGWH.symmetricOperatorObj.{u, v} n) = f.hom.natTrans.app n
  rw [component_comp, hc, h]
  change f.hom.natTrans.app n ≫ 𝟙 (K.X.functor.obj n) = f.hom.natTrans.app n
  exact Category.comp_id _

private theorem mapIso_counit_inv_component (H : OriginalModule.{u, v})
    (F : NativeCarrier.{u, v}) (e : H ≅ reconstructedModule F) (n : I) :
    component (moduleToOperator.{u, v}.mapIso e ≪≫ operatorRecoveryIso F).inv
        (PointedCGWH.symmetricOperatorObj.{u, v} n) = e.inv.hom.natTrans.app n := by
  let K := reconstructedModule F
  let f : K ⟶ H := e.inv
  have h := toOperatorMorphism_component f (PointedCGWH.symmetricOperatorObj.{u, v} n)
  have hc := operatorRecoveryIso_inv_component F (PointedCGWH.symmetricOperatorObj.{u, v} n)
  change component ((operatorRecoveryIso F).inv ≫ toOperatorMorphism f)
    (PointedCGWH.symmetricOperatorObj.{u, v} n) = f.hom.natTrans.app n
  rw [component_comp, hc, h]
  change 𝟙 (K.X.functor.obj n) ≫ f.hom.natTrans.app n = f.hom.natTrans.app n
  exact Category.id_comp _

/-- Every complete forward native object component retains the original beta map. -/
theorem objectIso_hom_beta (r : I) (M : V.{u, v}) (N : OriginalModule.{u, v}) (n : I) :
    component (objectIso r M N).hom (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      forwardLevel r M N n :=
  (mapIso_counit_hom_component (originalHom r M N) (target r M N) (moduleIso r M N) n).trans
    (moduleIso_hom_beta r M N n)

/-- Every complete inverse native object component retains the original end extension. -/
theorem objectIso_inv_beta (r : I) (M : V.{u, v}) (N : OriginalModule.{u, v}) (n : I) :
    component (objectIso r M N).inv (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      inverseLevel r M N n :=
  (mapIso_counit_inv_component (originalHom r M N) (target r M N) (moduleIso r M N) n).trans
    (moduleIso_inv_beta r M N n)


/-- The original forward comparison respects the entire original enriched Hom object. -/
theorem objectIso_fullHom (r : I) (M : V.{u, v}) (N : OriginalModule.{u, v})
    (x y : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry
        ((toOperatorFunctor (originalHom r M N)).toEnrichedFunctor.map x y) ≫
      component (objectIso r M N).hom y =
    (component (objectIso r M N).hom x ⊗ₘ 𝟙 (x ⟶[V.{u, v}] y)) ≫
      MonoidalClosed.uncurry ((target r M N).toEnrichedFunctor.map x y) :=
  GradedNatTrans.uncurriedNaturality (objectIso r M N).hom x y

/-- The inverse comparison respects the same complete original enriched Hom objects. -/
theorem objectIso_inv_fullHom (r : I) (M : V.{u, v}) (N : OriginalModule.{u, v})
    (x y : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry ((target r M N).toEnrichedFunctor.map x y) ≫
      component (objectIso r M N).inv y =
    (component (objectIso r M N).inv x ⊗ₘ 𝟙 (x ⟶[V.{u, v}] y)) ≫
      MonoidalClosed.uncurry
        ((toOperatorFunctor (originalHom r M N)).toEnrichedFunctor.map x y) :=
  GradedNatTrans.uncurriedNaturality (objectIso r M N).inv x y

end NativeOmegaRecovery.NativeSymmetricFreeFunction
