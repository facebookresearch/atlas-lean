/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.ModuleRightEvaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.CastLeftFamilyReadback

/-!
# Cast Day Right Readback

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

/-- The original right Day pair reads through both complete source preimages and free
adjunctions, the Day point, source action, evaluation comparison and native counit. -/
def CastDayRightFamilyReadback (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : originalTargetMonoidal S E = M)
    (p : Independent.PairFormula M (fun n K => Free.object (a n) K) (fun n r => T.obj (n, r))) : Prop :=
  letI := M
  ∀ (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a n) K ⟶ N)
    (g : Free.object (a r) L ⟶ 𝟙_ (EnrichedFunctorCat V J)),
    Free.evaluate (a (T.obj (n, r))) (K ⊗ L) N
      ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom) =
    (((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
        K (E.inverse.obj N) (sourcePreimage S E a h n K N f) ⊗ₘ
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S r).homEquiv
        L (𝟙_ (RightModule S))
        (sourcePreimage S E a h r L (E.functor.obj (𝟙_ (RightModule S)))
          (g ≫ eqToHom (congrArg (fun Z : MonoidalCategory (EnrichedFunctorCat V J) =>
            Z.tensorUnit) hM.symm)) ≫ E.unitIso.inv.app (𝟙_ (RightModule S)))) ≫
      EnrichedDayKernel.Generators.point T (E.inverse.obj N).X.toEnrichedFunctor S.toEnrichedFunctor (n, r) ≫
      component (tensorComparison.inv.app ((E.inverse.obj N).X, S) ≫ (E.inverse.obj N).action)
        (T.obj (n, r))) ≫
      (h (T.obj (n, r))).inv.app (E.inverse.obj N) ≫
      component (E.counitIso.hom.app N) (a (T.obj (n, r)))

/-- Eliminate the complete target tensor and pair-family casts before specializing the native
source; the literal Day point and every original source and target map are retained. -/
theorem cast_family_day_right_readback (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : originalTargetMonoidal S E = M)
    (hType : ModuleStage.SymbolicPair.FamilyType S E a (fun n r => T.obj (n, r)) =
      Independent.PairFormula M (fun n K => Free.object (a n) K) (fun n r => T.obj (n, r))) :
    CastDayRightFamilyReadback S E a h T tensorComparison M hM
      (cast hType (ModuleStage.SymbolicPair.pair S E a h (fun n r => T.obj (n, r))
        (fun n r K L => tensorComparison.app (Free.object n K, Free.object r L) ≪≫
          EnrichedDayKernel.FreePairComparison.iso T n r K L))) := by
  cases hM
  let := Monoidal.transport E
  intro n r K L N f g
  simpa only [CastDayRightFamilyReadback, ModuleStage.SymbolicPair.pair,
    sourcePreimage, cast_eq, eqToHom_refl,
    Category.comp_id, Category.assoc] using right_pair S E a h T tensorComparison n r K L N f g

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
