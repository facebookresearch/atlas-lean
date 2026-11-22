/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.TransportLeftAugment
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.ModulePairEvaluation

/-!
# Source Left Day Pair Evaluation

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
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction Enriched.prodCategory

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
  (T : EnrichedFunctor V (I × I) I)
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I),
    HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]
  [∀ (F : EnrichedFunctorCat V (I × I)) (k : I),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (I × I)) (k : I),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (I × I)) (k : I),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight T k) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight T k) F.toEnrichedFunctor)]
  (tensorComparison : tensor (EnrichedFunctorCat V I) ≅ EnrichedDayKernel.Input.bifunctor T)

private local instance constructionMonoidal1 : MonoidalCategory (RightModule S) := RightModuleFree.tensorMonoidal S

/-- The actual reconstructed native left pair retains both full source preimages, the original Day generator and source
  left action, and the entire target counit. -/
theorem left_pair (n r : I) (K L : V) (N : EnrichedFunctorCat V J) :
    letI := Monoidal.transport E
    ∀ (f : Free.object (a n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
      (g : Free.object (a r) L ⟶ N),
    Free.evaluate (a (T.obj (n, r))) (K ⊗ L) N
      ((ModuleStage.ofIso S E a h n r (T.obj (n, r)) K L
        (tensorComparison.app (Free.object n K, Free.object r L) ≪≫
          EnrichedDayKernel.FreePairComparison.iso T n r K L)).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) =
    (((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
        K (𝟙_ (RightModule S))
        (E.unitIso.hom.app ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj K) ≫
          E.inverse.map ((ModuleStage.sourceComparison S E a h n).hom.app K ≫ f) ≫
          E.unitIso.inv.app (𝟙_ (RightModule S))) ⊗ₘ
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S r).homEquiv
        L (E.inverse.obj N) (sourcePreimage S E a h r L N g)) ≫
      EnrichedDayKernel.Generators.point T S.toEnrichedFunctor (E.inverse.obj N).X.toEnrichedFunctor (n, r) ≫
      component (tensorComparison.inv.app (S, (E.inverse.obj N).X) ≫ leftAction S (E.inverse.obj N))
        (T.obj (n, r))) ≫
      (h (T.obj (n, r))).inv.app (E.inverse.obj N) ≫
      component (E.counitIso.hom.app N) (a (T.obj (n, r))) := by
  let := Monoidal.transport E
  intro f g
  let e := tensorComparison.app (Free.object n K, Free.object r L) ≪≫
    EnrichedDayKernel.FreePairComparison.iso T n r K L
  let es := ModuleStage.sourcePair S n r (T.obj (n, r)) K L e
  let ep := (ModuleStage.sourceComparison S E a h n).app K
  let eq := (ModuleStage.sourceComparison S E a h r).app L
  let er := (ModuleStage.sourceComparison S E a h (T.obj (n, r))).app (K ⊗ L)
  let sf := E.unitIso.hom.app ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj K) ≫
    E.inverse.map (ep.hom ≫ f) ≫ E.unitIso.inv.app (𝟙_ (RightModule S))
  let sg := sourcePreimage S E a h r L N g
  let sourceWord := es.inv ≫ (sf ⊗ₘ sg) ≫ (λ_ (E.inverse.obj N)).hom
  have hWord : (ModuleStage.ofIso S E a h n r (T.obj (n, r)) K L e).inv ≫
      (f ⊗ₘ g) ≫ (λ_ N).hom =
    er.inv ≫ E.functor.map sourceWord ≫ E.counitIso.hom.app N :=
      TransportAugment.left_word E ep eq er es f g
  have hRead := evaluate_from_source S E a h (T.obj (n, r)) (K ⊗ L)
    (E.inverse.obj N) N sourceWord (E.counitIso.hom.app N)
  have hDay := ModuleDayEvaluation.left_pair S T tensorComparison n r K L (E.inverse.obj N) sf sg
  change (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S (T.obj (n, r))).homEquiv
      (K ⊗ L) (E.inverse.obj N) sourceWord = _ at hDay
  rw [hDay] at hRead
  exact (congrArg (Free.evaluate (a (T.obj (n, r))) (K ⊗ L) N) hWord).trans hRead

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
