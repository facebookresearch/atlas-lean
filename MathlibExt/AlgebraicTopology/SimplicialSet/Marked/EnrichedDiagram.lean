/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SimplicialEnrichment

/-!
# Actual marked-valued enriched diagrams and whole natural maps

The objects are genuine enriched functors into the native marked
simplicial enrichment. A map between diagrams preserves the whole Hom
action, in every simplicial degree, rather than only the ordinary
zero-simplex naturality square. Composition retains the original marked
component maps. Object and scalar universes are independent.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

attribute [local instance] markedSimplicialCategory

/-- The original marked-valued enriched functor carrier, with its whole Hom actions. -/
abbrev EnrichedDiagram (C : Type v) [EnrichedCategory SSet.{u} C] :=
  EnrichedFunctor SSet.{u} C Marked.{u}

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- A genuine natural marked map commutes with every original enriched Hom simplex. -/
@[ext]
structure EnrichedDiagramMap (F G : EnrichedDiagram C) where
  /-- The original marked map at each individual source object. -/
  app (x : C) : F.obj x ⟶ G.obj x
  /-- Whole Hom naturality retains both actual marked actions and the supplied component maps. -/
  naturality (x y : C) :
    F.map x y ≫ mappingComplexPost .maximal (F.obj x) (app y) =
      G.map x y ≫ mappingComplexPre .maximal (app x) (G.obj y)

/-- Whole diagram maps are heterogeneously determined by their components under an actual target equality. -/
theorem EnrichedDiagramMap.hext {F G H : EnrichedDiagram C}
    (h : G = H) {α : EnrichedDiagramMap F G} {β : EnrichedDiagramMap F H}
    (ha : HEq α.app β.app) : HEq α β := by
  cases h
  apply heq_of_eq
  exact EnrichedDiagramMap.ext (eq_of_heq ha)

/-- Identity diagram maps preserve all original marked components and Hom actions. -/
def EnrichedDiagramMap.id (F : EnrichedDiagram C) : EnrichedDiagramMap F F where
  app x := 𝟙 (F.obj x)
  naturality x y := by
    rw [mappingComplexPost_id, mappingComplexPre_id]

/-- Whole enriched natural maps compose by the same original marked component composition. -/
def EnrichedDiagramMap.comp {F G H : EnrichedDiagram C}
    (α : EnrichedDiagramMap F G) (β : EnrichedDiagramMap G H) : EnrichedDiagramMap F H where
  app x := α.app x ≫ β.app x
  naturality x y := by
    rw [mappingComplexPost_comp, ← Category.assoc, α.naturality,
      Category.assoc, mappingComplexPre_post, ← Category.assoc, β.naturality,
      Category.assoc, ← mappingComplexPre_comp]

/-- The category of genuine marked enriched diagrams uses full, not merely vertex, naturality. -/
@[instance_reducible]
def enrichedDiagramCategory (C : Type v) [EnrichedCategory SSet.{u} C] :
    Category.{max u v} (EnrichedDiagram C) where
  Hom := EnrichedDiagramMap
  id := EnrichedDiagramMap.id
  comp := EnrichedDiagramMap.comp
  id_comp α := by ext x; exact Category.id_comp (α.app x)
  comp_id α := by ext x; exact Category.comp_id (α.app x)
  assoc α β γ := by ext x; exact Category.assoc (α.app x) (β.app x) (γ.app x)

attribute [local instance] enrichedDiagramCategory

/-- The whole original action square holds at every scalar simplex, retaining both marked prisms. -/
theorem EnrichedDiagramMap.naturality_app {F G : EnrichedDiagram C}
    (α : EnrichedDiagramMap F G) (x y : C) (n : ℕ) (f : (x ⟶[SSet.{u}] y) _⦋n⦌) :
    (F.map x y).app (op ⦋n⦌) f ≫ α.app y =
      prodMap (𝟙 (max (Δ[n] : SSet.{u}))) (α.app x) ≫
        (G.map x y).app (op ⦋n⦌) f :=
  congr($(α.naturality x y).app (op ⦋n⦌) f)

/-- Actual evaluation is a functor into the original marked category. -/
def enrichedDiagramEvaluation (C : Type v) [EnrichedCategory SSet.{u} C] (x : C) :
    @Functor (EnrichedDiagram C) (enrichedDiagramCategory C) Marked.{u} inferInstance where
  obj F := F.obj x
  map α := α.app x
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction along a genuine enriched source map retains its entire original action. -/
def enrichedDiagramRestrict {D : Type w} [EnrichedCategory SSet.{u} D]
    (A : EnrichedFunctor SSet.{u} D C) :
    @Functor (EnrichedDiagram C) (enrichedDiagramCategory C)
      (EnrichedDiagram D) (enrichedDiagramCategory D) where
  obj F := A.comp SSet.{u} F
  map α :=
    { app x := α.app (A.obj x)
      naturality x y := by
        dsimp only [EnrichedFunctor.comp]
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun t => A.map x y ≫ t) (α.naturality (A.obj x) (A.obj y))).trans
            (Category.assoc _ _ _).symm) }
  map_id _ := rfl
  map_comp _ _ := rfl

end SSet.Marked
