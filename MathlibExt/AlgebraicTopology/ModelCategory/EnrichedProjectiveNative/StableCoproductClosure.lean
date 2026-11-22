/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping
import MathlibExt.AlgebraicTopology.ModelCategory.SourceMappingWeakEquivalences
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalCoproductHomotopyClasses
import MathlibExt.Topology.Category.PointedCGWH.NativeMappingSourcePreservation

/-!
# Original native Omega tests under coproducts of cofibrant sources

The actual source-mapping functor carries each caller coproduct to its full
mapping product. Products of fibrant weak maps and the native mapping Hom
criterion give the original Omega tests of the caller's unchanged map.
-/

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.StableCoproductClosure

open OperatorStabilizationK

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {A L : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type w} [HasProductsOfShape J PointedCGWH.{u, v}]

/-- Every map of actual cofibrant source coproducts retains all original Omega-target Hom tests. -/
theorem omegaTests_of_cofibrantCofans (s : NativeStabilizationFamily.{u, v} A L)
    {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} A}
    [∀ j, IsCofibrant (X j)] [∀ j, IsCofibrant (Y j)]
    (c : Cofan X) (hc : IsColimit c) (d : Cofan Y) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.inj j ≫ p = f j ≫ d.inj j)
    (hf : ∀ j, NativeK.omegaTests s (f j)) : NativeK.omegaTests s p := by
  let _ : IsCofibrant c.pt := originalCofanPoint_cofibrant c hc
  let _ : IsCofibrant d.pt := originalCofanPoint_cofibrant d hd
  apply DerivedLocalMapping.omegaTests_of_mappingPre_weak s p
  intro E hE
  let F := PointedCGWH.NativeMappingSourceFunctor.source E
  let _ : PreservesLimitsOfSize.{w, w} F :=
    PointedCGWH.NativeMappingSourcePreservation.source_preservesLimitsOfSize E
  let _ : ∀ j, IsFibrant (F.obj (Opposite.op (X j))) :=
    fun j => PointedCGWH.modelCategory.allObjectsFibrant _
  let _ : ∀ j, IsFibrant (F.obj (Opposite.op (Y j))) :=
    fun j => PointedCGWH.modelCategory.allObjectsFibrant _
  have hMap : ∀ j, WeakEquivalence (F.map (f j).op) := by
    intro j
    exact (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (DerivedLocalMapping.mappingPre_weak_of_omegaTests s (f j) (hf j) E hE)
  have h := OriginalCoproductSourceMapping.originalCallerMap_weak F c hc d hd f p hp hMap
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp h

/-- The literal coproduct map of every cofibrant Omega-test family is an Omega-test equivalence. -/
theorem omegaTests_sigmaMap (s : NativeStabilizationFamily.{u, v} A L)
    [HasCoproductsOfShape J (EnrichedFunctorCat PointedCGWH.{u, v} A)]
    {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} A}
    [∀ j, IsCofibrant (X j)] [∀ j, IsCofibrant (Y j)]
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, NativeK.omegaTests s (f j)) :
    NativeK.omegaTests s (Limits.Sigma.map f) :=
  omegaTests_of_cofibrantCofans s (Cofan.mk (∐ X) (Sigma.ι X)) (coproductIsCoproduct X)
    (Cofan.mk (∐ Y) (Sigma.ι Y)) (coproductIsCoproduct Y) f (Limits.Sigma.map f)
    (fun j => Sigma.ι_map f j) hf

omit [HasProductsOfShape J PointedCGWH.{u, v}] in
/-- All original component Omega tests give every full Hom test of the actual derived coproduct map. -/
theorem omegaTests_derivedMap (s : NativeStabilizationFamily.{u, v} A L)
    [HasCoproductsOfShape J (EnrichedFunctorCat PointedCGWH.{u, v} A)]
    {X Y : J → EnrichedFunctorCat PointedCGWH.{u, v} A}
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, NativeK.omegaTests s (f j)) :
    NativeK.omegaTests s (OriginalDerivedCoproduct.map X f) := by
  intro E hE
  let _ : IsFibrant E := Native.allObjectsFibrant E
  exact OriginalDerivedCoproduct.map_precomp_bijective X
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) f (fun j => hf j E hE)

end HomotopicalAlgebra.EnrichedProjective.Native.StableCoproductClosure
