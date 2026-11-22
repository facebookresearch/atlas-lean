/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.CastDayRightReadback

/-!
# Original Day Right Readback

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uV vV uJ
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open CommutativeModuleConversion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  [EnrichedCategory V ℕ]
  [MonoidalCategory (EnrichedFunctorCat V ℕ)] [SymmetricCategory (EnrichedFunctorCat V ℕ)]
  (S : EnrichedFunctorCat V ℕ) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V ℕ)]
  [∀ X : EnrichedFunctorCat V ℕ, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V ℕ, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  (E : RightModule S ≌ EnrichedFunctorCat V J)
  (a : ℕ → J)
  (h : ∀ n, E.functor ⋙ evaluation (a n) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)
  (T : EnrichedFunctor V (ℕ × ℕ) ℕ)
  [∀ (F G : EnrichedFunctor V ℕ V) (k : ℕ), HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ (F G : EnrichedFunctor V ℕ V) (k : ℕ), HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ (F G : EnrichedFunctor V ℕ V) (k : ℕ),
    HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]
  [∀ (F : EnrichedFunctorCat V (ℕ × ℕ)) (k : ℕ),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (ℕ × ℕ)) (k : ℕ),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (ℕ × ℕ)) (k : ℕ),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight T k) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight T k) F.toEnrichedFunctor)]
  (tensorComparison : tensor (EnrichedFunctorCat V ℕ) ≅ EnrichedDayKernel.Input.bifunctor T)

private local instance constructionMonoidal1 : MonoidalCategory (RightModule S) := RightModuleFree.tensorMonoidal S

/-- Resolve the equality of the complete original diagram comparison before applying the
original tensor and pair-family casts; all source preimages and native target maps remain. -/
theorem cast_family_original_day_right_readback
    (e : ∀ (n r : ℕ) (K L : V), Free.object n K ⊗ Free.object r L ≅ Free.object (T.obj (n, r)) (K ⊗ L))
    (he : e = fun n r K L => tensorComparison.app (Free.object n K, Free.object r L) ≪≫
      EnrichedDayKernel.FreePairComparison.iso T n r K L)
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : originalTargetMonoidal S E = M)
    (hType : ModuleStage.SymbolicPair.FamilyType S E a (fun n r => T.obj (n, r)) =
      Independent.PairFormula M (fun n K => Free.object (a n) K) (fun n r => T.obj (n, r))) :
    CastDayRightFamilyReadback S E a h T tensorComparison M hM
      (cast hType (ModuleStage.SymbolicPair.pair S E a h (fun n r => T.obj (n, r)) e)) := by
  subst e
  exact cast_family_day_right_readback S E a h T tensorComparison M hM hType

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
