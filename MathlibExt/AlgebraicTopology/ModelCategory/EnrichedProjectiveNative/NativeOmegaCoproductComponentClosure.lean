/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeCofibrantComponents
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableCoproductClosure
import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Original coproduct Omega tests with cofibrant components

Evaluation preserves the actual native coproduct. Brown's original
cofibrant coproduct argument therefore proves level weakness of a
coproduct map whose components have cofibrant source and target objects.

Apply this to both entire original Q-counit families. The actual Q maps
have native cofibrant endpoints, so their coproduct has all Omega tests
by the original native coproduct theorem. The whole counit square and
two-out-of-three transfer the result to the original coproduct map.
Projective cofibrancy of the original target objects is not required.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.NativeOmegaCoproductComponentClosure

open OperatorStabilizationK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type w} [HasColimitsOfShape (Discrete J) PointedCGWH.{u, v}]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Every original coproduct map with cofibrant native components is
level weak when all of its original component maps are level weak. -/
theorem sigmaMap_levelWeak_of_componentCofibrant
    {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : ∀ j, X j ⟶ Y j)
    (hX : ∀ j a, IsCofibrant ((X j).toEnrichedFunctor.obj a))
    (hY : ∀ j a, IsCofibrant ((Y j).toEnrichedFunctor.obj a))
    (hf : ∀ j, weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) (f j)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) (Limits.Sigma.map f) := by
  apply (IndexCofibrantProperness.originalNativeLevelWeak_iff_evaluation
    (Limits.Sigma.map f)).mpr
  intro a
  let _ : ∀ j, IsCofibrant ((evaluation (V := PointedCGWH.{u, v}) a).obj (X j)) := fun j => hX j a
  let _ : ∀ j, IsCofibrant ((evaluation (V := PointedCGWH.{u, v}) a).obj (Y j)) := fun j => hY j a
  let _ : ∀ j, WeakEquivalence ((evaluation (V := PointedCGWH.{u, v}) a).map (f j)) :=
    fun j => (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      ((IndexCofibrantProperness.originalNativeLevelWeak_iff_evaluation (f j)).mp (hf j) a)
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    (weakEquivalence_of_cofibrantCoproductCocones
      (fun j => (evaluation (V := PointedCGWH.{u, v}) a).map (f j))
      (isColimitOfHasCoproductOfPreservesColimit (evaluation a) X)
      (isColimitOfHasCoproductOfPreservesColimit (evaluation a) Y)
      ((evaluation a).map (Limits.Sigma.map f)) (fun j => by
        change (evaluation a).map (Limits.Sigma.ι X j) ≫ (evaluation a).map (Limits.Sigma.map f) =
          (evaluation a).map (f j) ≫ (evaluation a).map (Limits.Sigma.ι Y j)
        rw [← Functor.map_comp, Limits.Sigma.ι_map, Functor.map_comp]))

/-- The actual full Q-counit family gives a level-weak comparison with
the original coproduct whenever its original components are cofibrant. -/
theorem originalQcounit_sigmaMap_levelWeak
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (X : J → EnrichedFunctorCat PointedCGWH.{u, v} I)
    (hX : ∀ j a, IsCofibrant ((X j).toEnrichedFunctor.obj a)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      (Limits.Sigma.map (fun j => (Replacement.cofibrantReplacementCounit (B := B)).app (X j))) :=
  sigmaMap_levelWeak_of_componentCofibrant
    (fun j => (Replacement.cofibrantReplacementCounit (B := B)).app (X j))
    (fun j => NativeCofibrantComponents.originalQ_allComponents_isCofibrant hHom (X j)) hX
    (fun j => Replacement.cofibrantReplacementCounit_mem_weakEquivalences (X j))

variable [HasProductsOfShape J PointedCGWH.{u, v}]

/-- All original coproduct Omega tests hold for maps with cofibrant
components at both original endpoints, without projective cofibrancy. -/
theorem sigmaMap_omegaTests_of_componentCofibrant
    (s : NativeStabilizationFamily.{u, v} I L)
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : ∀ j, X j ⟶ Y j)
    (hX : ∀ j a, IsCofibrant ((X j).toEnrichedFunctor.obj a))
    (hY : ∀ j a, IsCofibrant ((Y j).toEnrichedFunctor.obj a))
    (hf : ∀ j, NativeK.omegaTests s (f j)) :
    NativeK.omegaTests s (Limits.Sigma.map f) := by
  let Q := Replacement.cofibrantReplacement (B := B) (A := I)
  let p := Replacement.cofibrantReplacementCounit (B := B) (A := I)
  let W := NativeK.omegaTests s
  let _ : ∀ j, IsCofibrant (Q.obj (X j)) :=
    fun j => Replacement.isCofibrant_cofibrantReplacement (X j)
  let _ : ∀ j, IsCofibrant (Q.obj (Y j)) :=
    fun j => Replacement.isCofibrant_cofibrantReplacement (Y j)
  have hfQ : ∀ j, W (Q.map (f j)) := by
    intro j
    have hXQ : W (p.app (X j)) := NativeK.levelWeak_le_omegaTests s _
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (X j))
    have hYQ : W (p.app (Y j)) := NativeK.levelWeak_le_omegaTests s _
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (Y j))
    have h := W.comp_mem _ _ hXQ (hf j)
    rw [← Replacement.cofibrantReplacementCounit_naturality (f j)] at h
    exact W.of_postcomp _ _ hYQ h
  have hQ : W (Limits.Sigma.map (fun j => Q.map (f j))) :=
    StableCoproductClosure.omegaTests_sigmaMap s (fun j => Q.map (f j)) hfQ
  have hpX : W (Limits.Sigma.map (fun j => p.app (X j))) :=
    NativeK.levelWeak_le_omegaTests s _ (originalQcounit_sigmaMap_levelWeak hHom X hX)
  have hpY : W (Limits.Sigma.map (fun j => p.app (Y j))) :=
    NativeK.levelWeak_le_omegaTests s _ (originalQcounit_sigmaMap_levelWeak hHom Y hY)
  have hn : Limits.Sigma.map (fun j => Q.map (f j)) ≫
      Limits.Sigma.map (fun j => p.app (Y j)) =
      Limits.Sigma.map (fun j => p.app (X j)) ≫ Limits.Sigma.map f := by
    rw [Limits.Sigma.map_comp_map, Limits.Sigma.map_comp_map]
    congr 1
    funext j
    exact Replacement.cofibrantReplacementCounit_naturality (f j)
  have h := W.comp_mem _ _ hQ hpY
  rw [hn] at h
  exact W.of_precomp _ _ hpX h

end HomotopicalAlgebra.EnrichedProjective.Native.NativeOmegaCoproductComponentClosure
