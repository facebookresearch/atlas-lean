/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeImageUnits
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeCoefficientNaturality

/-!
# Whole native free and left-extension Hom naturality

Free coefficient changes use the existing free/evaluation adjunction.
The inverse native free-image comparison followed by an extended
source map reads the same original unit and whole universal map.
These equations keep the actual selected adjunctions and coequalizers.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The whole free Hom correspondence is natural in the actual coefficient map. -/
theorem enrichedFreeHomEquiv_pre (C : Type v) [EnrichedCategory SSet.{u} C]
    (c : C) {A B : Marked.{u}} (f : A ⟶ B) (F : EnrichedDiagram C)
    (α : enrichedFreeDiagram C c B ⟶ F) :
    enrichedFreeHomEquiv C c A F ((enrichedFreeDiagramFunctor C c).map f ≫ α) =
      f ≫ enrichedFreeHomEquiv C c B F α :=
  (enrichedFreeEvaluationAdjunction C c).homEquiv_naturality_left f α

/-- The whole free Hom correspondence is natural in the actual enriched target map. -/
theorem enrichedFreeHomEquiv_post (C : Type v) [EnrichedCategory SSet.{u} C]
    (c : C) (A : Marked.{u}) {F G : EnrichedDiagram C}
    (α : enrichedFreeDiagram C c A ⟶ F) (β : F ⟶ G) :
    enrichedFreeHomEquiv C c A G (α ≫ β) =
      enrichedFreeHomEquiv C c A F α ≫ β.app c := by
  change enrichedFreeUnit C c A ≫ (α.app c ≫ β.app c) =
    (enrichedFreeUnit C c A ≫ α.app c) ≫ β.app c
  exact (Category.assoc _ _ _).symm

/-- An actual extended source map followed by a whole target map has its original unit-natural universal image. -/
theorem enrichedLeftKan_universal_map_post {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D] (j : EnrichedFunctor SSet.{u} C D)
    {V W : EnrichedDiagram C} (φ : V ⟶ W) {F : EnrichedDiagram D}
    (g : EnrichedLeftKan.object j W ⟶ F) :
    EnrichedLeftKan.universalHomEquiv j V F ((EnrichedLeftKan.leftExtension j).map φ ≫ g) =
      φ ≫ EnrichedLeftKan.universalHomEquiv j W F g := by
  exact (EnrichedLeftKan.universalHomEquiv_natural_right j V (EnrichedLeftKan.map j φ) g).trans
    ((congrArg (fun f => f ≫ (enrichedDiagramRestrict j).map g)
      (EnrichedLeftKan.map_homEquiv j φ)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun f => φ ≫ f) (EnrichedLeftKan.universalHomEquiv_unit j W F g).symm)))

/-- The original inverse free-image mate and actual extended source map retain precisely their whole
  original free-unit universal readback. -/
theorem enrichedLeftKanFreeIso_inv_map_post {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D] (j : EnrichedFunctor SSet.{u} C D)
    (c : C) (A : Marked.{u}) {W : EnrichedDiagram C} (φ : enrichedFreeDiagram C c A ⟶ W)
    {F : EnrichedDiagram D} (g : EnrichedLeftKan.object j W ⟶ F) :
    enrichedFreeHomEquiv D (j.obj c) A F
        ((enrichedLeftKanFreeIso j c A).inv ≫ ((EnrichedLeftKan.leftExtension j).map φ ≫ g)) =
      enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict j).obj F)
        (φ ≫ EnrichedLeftKan.universalHomEquiv j W F g) :=
  (enrichedLeftKanFreeIso_inv_post j c A ((EnrichedLeftKan.leftExtension j).map φ ≫ g)).trans
    (congrArg (enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict j).obj F))
      (enrichedLeftKan_universal_map_post j φ g))

end SSet.Marked
