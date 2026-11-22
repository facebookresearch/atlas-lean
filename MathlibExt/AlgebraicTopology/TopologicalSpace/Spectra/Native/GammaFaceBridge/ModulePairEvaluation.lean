/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.TransportLeftAugment

/-!
# Module Pair Evaluation

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
  [BraidedCategory V] [MonoidalClosed V]
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

omit [SymmetricCategory (EnrichedFunctorCat V I)] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The right-module preimage of a native free map, formed from the source comparison and the unit
of `E`. -/
def sourcePreimage (n : I) (K : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a n) K ⟶ N) :
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj K ⟶ E.inverse.obj N :=
  E.unitIso.hom.app ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj K) ≫
    E.inverse.map ((ModuleStage.sourceComparison S E a h n).hom.app K ≫ f)

omit [SymmetricCategory (EnrichedFunctorCat V I)] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The complete original source preimage reconstructs every entire native free map. -/
theorem sourcePreimage_reconstruct (n : I) (K : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a n) K ⟶ N) :
    (ModuleStage.sourceComparison S E a h n).inv.app K ≫
      E.functor.map (sourcePreimage S E a h n K N f) ≫ E.counitIso.hom.app N = f := by
  rw [sourcePreimage, E.functor.map_comp]
  have hc := E.counitIso.hom.naturality ((ModuleStage.sourceComparison S E a h n).hom.app K ≫ f)
  change E.functor.map (E.inverse.map _) ≫ E.counitIso.hom.app N =
    E.counitIso.hom.app _ ≫ _ at hc
  simp only [Category.assoc]
  rw [hc]
  simp only [Functor.id_map]
  slice_lhs 2 3 =>
    dsimp only [Functor.comp_obj, Functor.id_obj]
    rw [E.functor_unitIso_comp]
  change ((ModuleStage.sourceComparison S E a h n).app K).inv ≫
      (𝟙 _ ≫ ((ModuleStage.sourceComparison S E a h n).app K).hom) ≫ f = f
  rw [Category.id_comp]
  exact ((ModuleStage.sourceComparison S E a h n).app K).inv_hom_id_assoc f

omit [SymmetricCategory (EnrichedFunctorCat V I)] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Original source and native free evaluation agree on the whole original preimage and counit. -/
theorem sourcePreimage_evaluate (n : I) (K : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a n) K ⟶ N) :
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
      K (E.inverse.obj N) (sourcePreimage S E a h n K N f) ≫
        (h n).inv.app (E.inverse.obj N) ≫ component (E.counitIso.hom.app N) (a n) =
      Free.evaluate (a n) K N f := by
  have hp := FreeAdjunctionSource.point E (a n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n) (h n)
    (sourcePreimage S E a h n K N f)
  have he := congrArg (fun z => z ≫ component (E.counitIso.hom.app N) (a n)) hp
  change (((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
      K (E.inverse.obj N) (sourcePreimage S E a h n K N f)) ≫ (h n).inv.app (E.inverse.obj N)) ≫
      (evaluation (a n)).map (E.counitIso.hom.app N) =
    Free.evaluate (a n) K (E.functor.obj (E.inverse.obj N))
      ((ModuleStage.sourceComparison S E a h n).inv.app K ≫
        E.functor.map (sourcePreimage S E a h n K N f)) ≫
      (evaluation (a n)).map (E.counitIso.hom.app N) at he
  rw [← Free.evaluate_postcomp] at he
  change (((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
      K (E.inverse.obj N) (sourcePreimage S E a h n K N f)) ≫ (h n).inv.app (E.inverse.obj N)) ≫
      component (E.counitIso.hom.app N) (a n) =
    Free.evaluate (a n) K N
      (((ModuleStage.sourceComparison S E a h n).inv.app K ≫
        E.functor.map (sourcePreimage S E a h n K N f)) ≫ E.counitIso.hom.app N) at he
  simp only [Category.assoc] at he
  rw [sourcePreimage_reconstruct S E a h n K N f] at he
  exact he

omit [SymmetricCategory (EnrichedFunctorCat V I)] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- An arbitrary complete source word and target map keep the original native free readback. -/
theorem evaluate_from_source (n : I) (K : V) (M : RightModule S)
    (N : EnrichedFunctorCat V J)
    (q : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj K ⟶ M)
    (g : E.functor.obj M ⟶ N) :
    Free.evaluate (a n) K N
      ((ModuleStage.sourceComparison S E a h n).inv.app K ≫ E.functor.map q ≫ g) =
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv K M q ≫
      (h n).inv.app M ≫ component g (a n) := by
  have hp := FreeAdjunctionSource.point E (a n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n) (h n) q
  change (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv K M q ≫
      (h n).inv.app M = Free.evaluate (a n) K (E.functor.obj M)
      ((ModuleStage.sourceComparison S E a h n).inv.app K ≫ E.functor.map q) at hp
  have hPost := Free.evaluate_postcomp (a n) K
    ((ModuleStage.sourceComparison S E a h n).inv.app K ≫ E.functor.map q) g
  change Free.evaluate (a n) K N
      (((ModuleStage.sourceComparison S E a h n).inv.app K ≫ E.functor.map q) ≫ g) =
    Free.evaluate (a n) K (E.functor.obj M)
      ((ModuleStage.sourceComparison S E a h n).inv.app K ≫ E.functor.map q) ≫ component g (a n) at hPost
  calc
    _ = Free.evaluate (a n) K N
        (((ModuleStage.sourceComparison S E a h n).inv.app K ≫ E.functor.map q) ≫ g) :=
      congrArg (Free.evaluate (a n) K N) (Category.assoc _ _ _).symm
    _ = _ := hPost
    _ = _ := (congrArg (fun z => z ≫ component g (a n)) hp.symm).trans (Category.assoc _ _ _)

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
