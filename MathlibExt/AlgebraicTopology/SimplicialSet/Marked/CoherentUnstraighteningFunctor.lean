/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningMarked

/-!
# Native coherent unstraightening on whole natural marked maps

Coefficient maps postcompose the original cone sections. They preserve
the exact original base simplex and all marked coefficient edges.
Whole ordinal restriction commutes with this actual composition, and
the identity and composition laws give a genuine functor into the
original marked slice. No family classification or Quillen comparison
is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

variable {C : Type u} [EnrichedCategory SSet.{u} C]

/-- A whole marked coefficient map postcomposes the original section and keeps the full original base simplex. -/
def UnstraighteningSimplex.mapCoefficient {F G : EnrichedDiagram Cᵒᵖ}
    (φ : F ⟶ G) {n : ℕ} (a : UnstraighteningSimplex F n) : UnstraighteningSimplex G n where
  base := a.base
  sectionMap := EnrichedDiagramMap.comp a.sectionMap
    ((enrichedDiagramRestrict a.base.opposite).map φ)

/-- The entire original marked section is followed by the same original coefficient map. -/
theorem UnstraighteningSimplex.mapCoefficient_section {F G : EnrichedDiagram Cᵒᵖ}
    (φ : F ⟶ G) {n : ℕ} (a : UnstraighteningSimplex F n) (i : (Index.{u} n)ᵒᵖ) :
    (a.mapCoefficient φ).sectionMap.app i = a.sectionMap.app i ≫ φ.app (op (a.base.obj i.unop)) := rfl

/-- Original ordinal restriction commutes with the actual whole marked coefficient map. -/
theorem UnstraighteningSimplex.mapCoefficient_pull {F G : EnrichedDiagram Cᵒᵖ}
    (φ : F ⟶ G) {n m : ℕ} (f : Vertex.{u} m →o Vertex.{u} n)
    (a : UnstraighteningSimplex F n) : (a.mapCoefficient φ).pull f = (a.pull f).mapCoefficient φ := by
  apply UnstraighteningSimplex.ext rfl
  apply heq_of_eq
  apply EnrichedDiagramMap.ext
  funext i
  exact (Category.assoc _ _ _).symm

/-- Identity coefficient maps retain every original unstraightening simplex and its full marked section. -/
theorem UnstraighteningSimplex.mapCoefficient_id {F : EnrichedDiagram Cᵒᵖ} {n : ℕ}
    (a : UnstraighteningSimplex F n) : a.mapCoefficient (𝟙 F) = a := by
  apply UnstraighteningSimplex.ext rfl
  apply heq_of_eq
  apply EnrichedDiagramMap.ext
  funext i
  exact Category.comp_id (a.sectionMap.app i)

/-- Consecutive actual coefficient maps have their original source-first composition on every section. -/
theorem UnstraighteningSimplex.mapCoefficient_comp {F G H : EnrichedDiagram Cᵒᵖ}
    (φ : F ⟶ G) (ψ : G ⟶ H) {n : ℕ} (a : UnstraighteningSimplex F n) :
    a.mapCoefficient (φ ≫ ψ) = (a.mapCoefficient φ).mapCoefficient ψ := by
  apply UnstraighteningSimplex.ext rfl
  apply heq_of_eq
  apply EnrichedDiagramMap.ext
  funext i
  exact (Category.assoc _ _ _).symm

/-- The native unstraightening map retains every whole original coherent simplex and marked section. -/
def coherentUnstraighteningMap {F G : EnrichedDiagram Cᵒᵖ} (φ : F ⟶ G) :
    coherentUnstraightening C F ⟶ coherentUnstraightening C G where
  hom :=
    { app n := ↾fun a => a.mapCoefficient φ
      naturality n m f := by
        ext a
        exact (UnstraighteningSimplex.mapCoefficient_pull φ f.unop.toOrderHom.uliftMap a).symm }
  preserve {e} he :=
    (φ.app (op (e.base.obj (SimplicialThickening.mk zeroOne)))).preserve he

/-- Every original marked coefficient map retains the exact whole base equation. -/
theorem coherentUnstraighteningMap_over {F G : EnrichedDiagram Cᵒᵖ} (φ : F ⟶ G) :
    coherentUnstraighteningMap φ ≫ coherentUnstraighteningProjection C G =
      coherentUnstraighteningProjection C F := Hom.ext rfl

/-- The actual one-fold coherent unstraightening functor takes whole marked natural maps to original same-base maps. -/
def coherentUnstraighteningFunctor (C : Type u) [EnrichedCategory SSet.{u} C] :
    EnrichedDiagram Cᵒᵖ ⥤ Over (max (coherentBase C)) where
  obj F := Over.mk (coherentUnstraighteningProjection C F)
  map φ := Over.homMk (coherentUnstraighteningMap φ) (coherentUnstraighteningMap_over φ)
  map_id F := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    ext n a
    exact UnstraighteningSimplex.mapCoefficient_id a
  map_comp φ ψ := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    ext n a
    exact UnstraighteningSimplex.mapCoefficient_comp φ ψ a

end SSet.Marked.CoherentWeight
