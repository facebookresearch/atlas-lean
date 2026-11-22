/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SourceLeftPairReadback

/-!
# Left Family Readback

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

/-- Evaluation of a native left-unit free pair equals evaluation of its two right-module preimages
and the source left unitor. -/
def LeftFamilyReadback (t : I → I → I)
    (e : ∀ (n r : I) (K L : V), Free.object n K ⊗ Free.object r L ≅ Free.object (t n r) (K ⊗ L))
    (p : ModuleStage.SymbolicPair.FamilyType S E a t) : Prop :=
  letI := Monoidal.transport E
  ∀ (n r : I) (K L : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
    (g : Free.object (a r) L ⟶ N),
    Free.evaluate (a (t n r)) (K ⊗ L) N
      ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) =
    Free.evaluate (t n r) (K ⊗ L) (E.inverse.obj N).X
      ((e n r K L).inv ≫
        ((RightModuleFree.freeGenerator S (Free.object n K) ≫
          (sourcePreimage S E a h n K (𝟙_ (EnrichedFunctorCat V J)) f ≫
            E.unitIso.inv.app (𝟙_ (RightModule S))).hom) ⊗ₘ
          (RightModuleFree.freeGenerator S (Free.object r L) ≫
            (sourcePreimage S E a h r L N g).hom)) ≫ leftAction S (E.inverse.obj N)) ≫
      (h (t n r)).inv.app (E.inverse.obj N) ≫
        component (E.counitIso.hom.app N) (a (t n r))

/-- The whole original native pair family reads through the unchanged free source family,
with all coefficient objects, source preimages and native target maps retained. -/
theorem left_family_readback (t : I → I → I)
    (e : ∀ (n r : I) (K L : V), Free.object n K ⊗ Free.object r L ≅ Free.object (t n r) (K ⊗ L)) :
    LeftFamilyReadback S E a h t e (ModuleStage.SymbolicPair.pair S E a h t e) := by
  let := Monoidal.transport E
  intro n r K L N f g
  change Free.evaluate (a (t n r)) (K ⊗ L) N
    ((ModuleStage.ofIso S E a h n r (t n r) K L (e n r K L)).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) = _
  exact left_pair_readback S E a h n r (t n r) K L (e n r K L) N f g

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
