/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback
import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingGenerators

/-!
# Left Day Action

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
  MonoidalLeftAction.monoidalOppositeLeftAction

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.ModuleLeftAction
open CommutativeModuleConversion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (b : EnrichedBraidedMonoidalCategoryData V I d)

/-- The Day generator formula for a left module action: braid the factors, apply the right action,
and undo the index braid. -/
def LeftActionFormula (S : EnrichedFunctorCat V I) : Prop :=
  letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  letI := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
  ∀ [MonObj S] (N : RightModule S) (n r : I),
    EnrichedDayKernel.Generators.point d.tensorEnrichedFunctor S.toEnrichedFunctor N.X.toEnrichedFunctor (n, r) ≫
      component (leftAction S N) (n ⊗ r) =
    (β_ (S.toEnrichedFunctor.obj n) (N.X.toEnrichedFunctor.obj r)).hom ≫
      EnrichedDayKernel.Generators.point d.tensorEnrichedFunctor N.X.toEnrichedFunctor S.toEnrichedFunctor (r, n) ≫
        component N.action (r ⊗ n) ≫ N.X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ n r).inv

theorem left_action (S : EnrichedFunctorCat V I) : LeftActionFormula d b S := by
  let := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  let := EnrichedDayKernel.BraidingMonoidal.symmetricCategory d b
  intro hS N n r
  let F := S.toEnrichedFunctor
  let G := N.X.toEnrichedFunctor
  have hB := EnrichedDayKernel.BraidingGenerators.unitGenerator_braid d F G b (n, r)
  have hNat := (ordinaryNatTrans N.action).naturality (β_ n r).inv
  change (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor G F).toOrdinaryFunctor.map (β_ n r).inv ≫
      component N.action (n ⊗ r) =
    component N.action (r ⊗ n) ≫ G.toOrdinaryFunctor.map (β_ n r).inv at hNat
  have hComponent : component (leftAction S N) (n ⊗ r) =
      EnrichedDayKernel.BraidingComponents.component d b F G (n ⊗ r) ≫
        component N.action (n ⊗ r) := by
    change component ((β_ S N.X).hom ≫ N.action) (n ⊗ r) = _
    rw [component_comp]
    exact congrArg (fun z => z ≫ component N.action (n ⊗ r))
      (EnrichedDayKernel.BraidingMonoidal.braiding_hom_component d b S N.X (n ⊗ r))
  have hB' : EnrichedDayKernel.Generators.point d.tensorEnrichedFunctor F G (n, r) ≫
      EnrichedDayKernel.BraidingComponents.component d b F G (n ⊗ r) =
    (β_ (F.obj n) (G.obj r)).hom ≫
      EnrichedDayKernel.Generators.point d.tensorEnrichedFunctor G F (r, n) ≫
        (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor G F).toOrdinaryFunctor.map (β_ n r).inv := by
    simpa only [EnrichedDayKernel.Generators.point,
      EnrichedDayKernel.AssociatorUnit.unitGenerator,
      EnrichedDayKernel.AssociatorUnit.identityInsert,
      EnrichedFunctor.externalTensor_obj, Category.assoc] using hB
  rw [hComponent, ← Category.assoc, hB']
  simp only [Category.assoc]
  rw [hNat]

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.ModuleLeftAction
