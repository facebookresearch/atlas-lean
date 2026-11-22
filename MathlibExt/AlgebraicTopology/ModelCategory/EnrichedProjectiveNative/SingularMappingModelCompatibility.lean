/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.SimplicialEnrichment
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IntervalModel
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelFibrancy
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedMapping.StrictComparison
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison
public import MathlibExt.Topology.Category.PointedCGWH.NativeCurrentBrownMapping

/-!
# Native singular mapping objects and the original level model

The selected pointed CGWH weak class is exactly detected by the actual
singular functor. Native Brown source invariance and the proved native
tensor/mapping Quillen adjunction therefore give both simplicial mapping
invariance laws on the unchanged enriched diagram carrier.

These laws construct the homotopy-function-complex invariance data. The
strict-to-derived comparison uses the framework's actual chosen replacement
maps and is weak on cofibrant sources. No model, invariance or derived-local
equivalence outcome is supplied as an additional native hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra PointedCGWH.SingularHomotopyGeometry
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.SingularMapping

/-- The actual singular map detects the selected original pointed CGWH
weak class in both directions. -/
theorem singularFunctor_weak_iff {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    SSet.realizationWeakEquivalences (singularFunctor.map f) ↔
      weakEquivalences PointedCGWH.{u, v} f := by
  let : SSet.KanComplex (singularFunctor.obj X) :=
    TopCat.toSSet_obj_kanComplex (CGWH.cgwhToTop.obj X.right)
  let : SSet.KanComplex (singularFunctor.obj Y) :=
    TopCat.toSSet_obj_kanComplex (CGWH.cgwhToTop.obj Y.right)
  rw [← HomotopicalAlgebra.weakEquivalence_iff f, PointedCGWH.weakEquivalence_iff f,
    CGWH.modelCategory.weakEquivalence_iff f.right]
  change SSet.realizationWeakEquivalences (singularFunctor.map f) ↔
    SSet.KanComplex.W (singularFunctor.map f)
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).symm

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory

/-- The original native model supplies its complete cofibrant/trivial-fibrant factorization. -/
local instance cofibrantFactorization :
    CategoryTheory.MorphismProperty.HasFunctorialFactorization
      (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I))
      (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)) :=
  Native.functorialFactorizations.1

/-- The original native model supplies its complete trivial-cofibrant/fibrant factorization. -/
local instance fibrantFactorization :
    CategoryTheory.MorphismProperty.HasFunctorialFactorization
      (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I))
      (fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)) :=
  Native.functorialFactorizations.2

/-- The full original simplicial source map is weak for a weak arrow between cofibrant diagrams. -/
theorem source_weak
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    [IsCofibrant X] [IsCofibrant Y]
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f)
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f.op).app Z) := by
  let : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff _).mpr hf
  let : IsFibrant Z := Native.allObjectsFibrant Z
  rw [SimplicialEnrichment.source_map]
  apply (singularFunctor_weak_iff _).mpr
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    (PointedCGWH.NativeCurrentBrownMapping.source_weak f Z)

/-- The full original simplicial target map is weak for every weak native target arrow. -/
theorem target_weak (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X]
    {Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I} (g : Y ⟶ Z)
    (hg : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) g) :
    SSet.realizationWeakEquivalences
      (((SimplicialCategory.sHomFunctor
        (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj (Opposite.op X)).map g) := by
  let : WeakEquivalence g := (HomotopicalAlgebra.weakEquivalence_iff _).mpr hg
  let : IsFibrant Y := Native.allObjectsFibrant Y
  let : IsFibrant Z := Native.allObjectsFibrant Z
  let : (PointedCGWH.EnrichedFunctorMapping.tensorMappingAdjunction X).IsQuillenAdjunction :=
    PointedCGWH.EnrichedIntervalCylinderModel.coefficient_isQuillen X
  rw [SimplicialEnrichment.target_map]
  apply (singularFunctor_weak_iff _).mpr
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := PointedCGWH.EnrichedFunctorMapping.tensorMappingAdjunction X) g)

/-- Native source invariance constructs the original chosen function-complex source data. -/
theorem precompData : HomotopyFunctionComplexPrecompData
    (C := EnrichedFunctorCat PointedCGWH.{u, v} I) where
  precompWeakOfWeakEquivalence {X} {Y} f hX hY hf Z _hZ := by
    let : IsCofibrant X := hX
    let : IsCofibrant Y := hY
    exact source_weak f hf Z

/-- Both native variance laws construct the chosen homotopy-function-complex invariance data. -/
theorem invarianceData : HomotopyFunctionComplexInvarianceData
    (C := EnrichedFunctorCat PointedCGWH.{u, v} I) where
  toHomotopyFunctionComplexPrecompData := precompData
  postcompWeakOfWeakEquivalence X hX {Y} {Z} g _hY _hZ hg := by
    let : IsCofibrant X := hX
    exact target_weak X g hg

/-- At cofibrant native endpoints the complete chosen derived map is weak exactly when its
original strict simplicial mapping map is weak. -/
theorem derivedPrecomp_weak_iff_strict
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    [IsCofibrant X] [IsCofibrant Y]
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := EnrichedFunctorCat PointedCGWH.{u, v} I) f Z) ↔
      SSet.realizationWeakEquivalences
        (((SimplicialCategory.sHomFunctor
          (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f.op).app Z) := by
  let : IsFibrant Z := Native.allObjectsFibrant Z
  let t := strictToDerivedMappingObject (C := EnrichedFunctorCat PointedCGWH.{u, v} I)
  have hX := strictToDerivedMappingObject_app_mem_realizationWeakEquivalences
    invarianceData X Z
  have hY := strictToDerivedMappingObject_app_mem_realizationWeakEquivalences
    invarianceData Y Z
  have hNatural := congrArg (fun η => η.app Z) (t.naturality f.op)
  change ((SimplicialCategory.sHomFunctor
      (EnrichedFunctorCat PointedCGWH.{u, v} I)).map f.op).app Z ≫
        (t.app (Opposite.op X)).app Z =
    (t.app (Opposite.op Y)).app Z ≫
      derivedMappingPrecomp (C := EnrichedFunctorCat PointedCGWH.{u, v} I) f Z at hNatural
  constructor
  · intro h
    have hComposite := SSet.realizationWeakEquivalences.comp_mem _ _ hY h
    rw [← hNatural] at hComposite
    exact SSet.realizationWeakEquivalences.of_postcomp _ _ hX hComposite
  · intro h
    have hComposite := SSet.realizationWeakEquivalences.comp_mem _ _ h hX
    rw [hNatural] at hComposite
    exact SSet.realizationWeakEquivalences.of_precomp _ _ hY hComposite

end HomotopicalAlgebra.EnrichedProjective.Native.SingularMapping
