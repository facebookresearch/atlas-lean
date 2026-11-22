/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningSimplex

/-!
# Actual target naturality of original native simplex charts

The original slice pullback adjunction and native Yoneda read every
whole coefficient map as its actual unstraightening simplex map.
Together with the proved full left-extension Hom naturality this
proves the entire chart correspondence is natural, retaining its
original unit, base simplex and marked section.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The native simplex correspondence reads the actual original inverse pullback-adjunction map by Yoneda. -/
theorem nativeSimplexUnHomEquiv_val (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ)
    (f : nativeSimplexBasis B n σ ⟶ (nativeUnstraightening B).obj F) :
    (nativeSimplexUnHomEquiv B n σ F f).val =
      SSet.yonedaEquiv
        (((Over.mapPullbackAdj (maximal.map (unit B))).homEquiv (nativeSimplexBasis B n σ)
          ((coherentUnstraighteningFunctor (realization B)).obj F)).symm f).left.hom := rfl

/-- Whole marked coefficient postcomposition acts on precisely the original unstraightening simplex data. -/
theorem nativeSimplexUnHomEquiv_post_val (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    {F G : EnrichedDiagram (realization B)ᵒᵖ}
    (f : nativeSimplexBasis B n σ ⟶ (nativeUnstraightening B).obj F) (φ : F ⟶ G) :
    (nativeSimplexUnHomEquiv B n σ G (f ≫ (nativeUnstraightening B).map φ)).val =
      (nativeSimplexUnHomEquiv B n σ F f).val.mapCoefficient φ := by
  let a := Over.mapPullbackAdj (maximal.map (unit B))
  let K := nativeSimplexBasis B n σ
  let U := coherentUnstraighteningFunctor (realization B)
  have h := a.homEquiv_naturality_right_symm f (U.map φ)
  exact congrArg (fun g : (Over.map (maximal.map (unit B))).obj K ⟶ U.obj G =>
    SSet.yonedaEquiv g.left.hom) h

/-- The actual simplex chart correspondence retains its exact original fixed-base cone section. -/
theorem nativeSimplexChartHomEquiv_section (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) (f : nativeSimplexChart B n σ ⟶ F) :
    nativeSimplexUnHomEquiv B n σ F (nativeSimplexChartHomEquiv B n σ F f) =
      (fixedSectionEquiv F (simplexInto B σ)).symm
        (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram n) F f) :=
  (nativeSimplexUnHomEquiv B n σ F).apply_symm_apply _

/-- The fixed original cone section postcomposes the same entire marked coefficient map. -/
theorem fixedSectionEquiv_mapCoefficient {C : Type u} [EnrichedCategory SSet.{u} C]
    {F G : EnrichedDiagram Cᵒᵖ} (φ : F ⟶ G) {n : ℕ}
    (σ : EnrichedFunctor SSet.{u} (Index.{u} n) C)
    (a : EnrichedDiagramMap (coneDiagram n) (simplexCoefficient F σ)) :
    ((fixedSectionEquiv G σ).symm (a ≫ (enrichedDiagramRestrict σ.opposite).map φ)).val =
      ((fixedSectionEquiv F σ).symm a).val.mapCoefficient φ := rfl

/-- The genuine whole native simplex-chart Hom correspondence is natural for every original marked coefficient map. -/
theorem nativeSimplexChartHomEquiv_natural_right (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    {F G : EnrichedDiagram (realization B)ᵒᵖ}
    (f : nativeSimplexChart B n σ ⟶ F) (φ : F ⟶ G) :
    nativeSimplexChartHomEquiv B n σ G (f ≫ φ) =
      nativeSimplexChartHomEquiv B n σ F f ≫ (nativeUnstraightening B).map φ := by
  apply (nativeSimplexUnHomEquiv B n σ G).injective
  apply Subtype.ext
  have hl := congrArg Subtype.val (nativeSimplexChartHomEquiv_section B n σ G (f ≫ φ))
  have hr := congrArg (fun a => a.val.mapCoefficient φ) (nativeSimplexChartHomEquiv_section B n σ F f)
  have hn := EnrichedLeftKan.universalHomEquiv_natural_right
    (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram n) f φ
  calc
    (nativeSimplexUnHomEquiv B n σ G (nativeSimplexChartHomEquiv B n σ G (f ≫ φ))).val =
        ((fixedSectionEquiv G (simplexInto B σ)).symm
          (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
            (coneDiagram n) G (f ≫ φ))).val := hl
    _ = ((fixedSectionEquiv F (simplexInto B σ)).symm
        (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
          (coneDiagram n) F f)).val.mapCoefficient φ :=
      (congrArg (fun a => ((fixedSectionEquiv G (simplexInto B σ)).symm a).val) hn).trans
        (fixedSectionEquiv_mapCoefficient φ (simplexInto B σ) _)
    _ = (nativeSimplexUnHomEquiv B n σ F (nativeSimplexChartHomEquiv B n σ F f)).val.mapCoefficient φ := hr.symm
    _ = (nativeSimplexUnHomEquiv B n σ G
        (nativeSimplexChartHomEquiv B n σ F f ≫ (nativeUnstraightening B).map φ)).val :=
      (nativeSimplexUnHomEquiv_post_val B n σ _ φ).symm

end SSet.Marked
