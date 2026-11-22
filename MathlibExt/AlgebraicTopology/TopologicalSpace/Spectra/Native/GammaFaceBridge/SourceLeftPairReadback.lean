/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.ModulePairEvaluation

/-!
# Source Left Pair Readback

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uV vV uI uJ
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash
open CommutativeModuleConversion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)] [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  (E : RightModule S ≌ EnrichedFunctorCat V J)
  (a : I → J)
  (h : ∀ n, E.functor ⋙ evaluation (a n) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)

private local instance constructionMonoidal1 : MonoidalCategory (RightModule S) := RightModuleFree.tensorMonoidal S

/-- For one free pair, evaluation after the native left unitor agrees with evaluation of the
source preimages and source left unitor. -/
def LeftPairReadback (n r t : I) (K L : V)
    (e : Free.object n K ⊗ Free.object r L ≅ Free.object t (K ⊗ L))
    (N : EnrichedFunctorCat V J) : Prop :=
  letI := Monoidal.transport E
  ∀ (f : Free.object (a n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
    (g : Free.object (a r) L ⟶ N),
    Free.evaluate (a t) (K ⊗ L) N
      ((ModuleStage.ofIso S E a h n r t K L e).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) =
    Free.evaluate t (K ⊗ L) (E.inverse.obj N).X
      (e.inv ≫
        ((RightModuleFree.freeGenerator S (Free.object n K) ≫
          (sourcePreimage S E a h n K (𝟙_ (EnrichedFunctorCat V J)) f ≫
            E.unitIso.inv.app (𝟙_ (RightModule S))).hom) ⊗ₘ
          (RightModuleFree.freeGenerator S (Free.object r L) ≫
            (sourcePreimage S E a h r L N g).hom)) ≫ leftAction S (E.inverse.obj N)) ≫
      (h t).inv.app (E.inverse.obj N) ≫ component (E.counitIso.hom.app N) (a t)

/-- Every arbitrary native left-unit free pair reads through its two original source free
adjunctions and its actual complete source action. -/
theorem left_pair_readback (n r t : I) (K L : V)
    (e : Free.object n K ⊗ Free.object r L ≅ Free.object t (K ⊗ L))
    (N : EnrichedFunctorCat V J) : LeftPairReadback S E a h n r t K L e N := by
  let := Monoidal.transport E
  intro f g
  let sf := sourcePreimage S E a h n K (𝟙_ (EnrichedFunctorCat V J)) f ≫
    E.unitIso.inv.app (𝟙_ (RightModule S))
  let sg := sourcePreimage S E a h r L N g
  let w := (ModuleStage.sourcePair S n r t K L e).inv ≫ (sf ⊗ₘ sg) ≫ (λ_ (E.inverse.obj N)).hom
  have hWord :
      (ModuleStage.ofIso S E a h n r t K L e).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom =
      (ModuleStage.sourceComparison S E a h t).inv.app (K ⊗ L) ≫
        E.functor.map w ≫ E.counitIso.hom.app N := by
    simpa only [ModuleStage.ofIso, sf, sg, w, sourcePreimage, Iso.app_hom, Iso.app_inv,
      Category.assoc] using
      TransportAugment.left_word E
      ((ModuleStage.sourceComparison S E a h n).app K)
      ((ModuleStage.sourceComparison S E a h r).app L)
      ((ModuleStage.sourceComparison S E a h t).app (K ⊗ L))
      (ModuleStage.sourcePair S n r t K L e) f g
  have hEval := congrArg (Free.evaluate (a t) (K ⊗ L) N) hWord
  have hRead := evaluate_from_source S E a h t (K ⊗ L) (E.inverse.obj N) N w
    (E.counitIso.hom.app N)
  have hSource := ModuleAdjunct.left_pair S n r t K L e (E.inverse.obj N) sf sg
  have hSource' := congrArg (fun z => z ≫ (h t).inv.app (E.inverse.obj N) ≫
    component (E.counitIso.hom.app N) (a t)) hSource
  exact hEval.trans (hRead.trans hSource')

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
