/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomCompositionUniverse
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpIndexedCoproductMaps
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ProductProjectionSharp
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
import MathlibExt.AlgebraicTopology.ModelCategory.SharpOverWeakBaseChange

/-!
# Full original universal Hom-composition graph

Keep every original ordered object pair and every original Hom
coefficient. The actual indexed coproduct of composition graphs is weak
for original groupoid components. Both full original coproduct projections
are sharp, so every complete native base change remains weak.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomUniversalGraph
open EnrichedHomCompositionFamilies

variable (C : Carrier.{u})

/-- The full original parameter Hom at its SAME original ordered pair. -/
abbrev parameters (i : C × C) : SSet.{u} := i.1 ⟶[SSet.{u}] i.2

/-- The full original source coefficient and parameter. -/
abbrev sourceCoefficients (z : C) (i : C × C) : SSet.{u} :=
  (z ⟶[SSet.{u}] i.1) ⊗ parameters C i

/-- The full original target coefficient and SAME whole parameter. -/
abbrev targetCoefficients (z : C) (i : C × C) : SSet.{u} :=
  (z ⟶[SSet.{u}] i.2) ⊗ parameters C i

/-- The complete original parameter coproduct, retaining every ordered object pair. -/
abbrev base : SSet.{u} := ∐ (parameters C)
/-- The complete original source coproduct of coefficients and full parameters. -/
abbrev source (z : C) : SSet.{u} := ∐ (sourceCoefficients C z)
/-- The complete original target coproduct with every same full parameter. -/
abbrev target (z : C) : SSet.{u} := ∐ (targetCoefficients C z)

/-- The SAME entire original source parameter projection at EVERY original pair. -/
def sourceProjection (z : C) : source C z ⟶ base C :=
  Limits.Sigma.map (fun i : C × C => snd (z ⟶[SSet.{u}] i.1) (parameters C i))

/-- The SAME entire original target parameter projection at EVERY original pair. -/
def targetProjection (z : C) : target C z ⟶ base C :=
  Limits.Sigma.map (fun i : C × C => snd (z ⟶[SSet.{u}] i.2) (parameters C i))

/-- Every SAME full original enriched composition graph is retained at its original pair. -/
def comparison (z : C) : source C z ⟶ target C z :=
  Limits.Sigma.map (fun i : C × C => postGraph z i.1 i.2)

/-- The full original comparison preserves the SAME entire parameter projection. -/
@[reassoc]
lemma comparison_projection (z : C) : comparison C z ≫ targetProjection C z = sourceProjection C z := by
  apply Sigma.hom_ext
  intro i
  simp only [comparison, targetProjection, sourceProjection, Sigma.ι_map_assoc,
    Sigma.ι_map, postGraph_snd_assoc]

/-- The entire original universal comparison is genuinely weak. -/
theorem comparison_weak [IsGroupoid (ComponentCategory.objects.{u} C)] (z : C) :
    SSet.realizationWeakEquivalences (comparison C z) :=
  SSet.sigma_map_mem_realizationWeakEquivalences _
    (fun i => postGraph_weak_universe C z i.1 i.2)

/-- The SAME original source projection is sharp, without original Hom Kan premises. -/
theorem sourceProjection_sharp (z : C) :
    MorphismProperty.sharpMaps SSet.realizationWeakEquivalences (sourceProjection C z) :=
  SSet.sharpMaps_sigmaMap _ (fun i =>
    SSet.ProductProjectionSharp.projection_sharp (z ⟶[SSet.{u}] i.1) (parameters C i))

/-- The SAME original target projection is sharp, without original Hom Kan premises. -/
theorem targetProjection_sharp (z : C) :
    MorphismProperty.sharpMaps SSet.realizationWeakEquivalences (targetProjection C z) :=
  SSet.sharpMaps_sigmaMap _ (fun i =>
    SSet.ProductProjectionSharp.projection_sharp (z ⟶[SSet.{u}] i.2) (parameters C i))

/-- The SAME full universal composition graph as an original over-map. -/
def overComparison (z : C) : Over.mk (sourceProjection C z) ⟶ Over.mk (targetProjection C z) :=
  Over.homMk (comparison C z) (comparison_projection C z)

/-- The SAME complete original native base change, with every original pair and parameter retained. -/
def baseChangeComparison (z : C) {T : SSet.{u}} (b : T ⟶ base C) :
    pullback (sourceProjection C z) b ⟶ pullback (targetProjection C z) b :=
  ((Over.pullback b).map (overComparison C z)).left

/-- EVERY full original base change is weak for original groupoid components. -/
theorem baseChangeComparison_weak [IsGroupoid (ComponentCategory.objects.{u} C)]
    (z : C) {T : SSet.{u}} (b : T ⟶ base C) :
    SSet.realizationWeakEquivalences (baseChangeComparison C z b) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  exact SharpOverWeakBaseChange.pullback_map_weak b (overComparison C z) (comparison_weak C z)
    (sourceProjection_sharp C z) (targetProjection_sharp C z)

end CategoryTheory.SimplicialEnrichment.EnrichedHomUniversalGraph
