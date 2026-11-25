/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagram

/-!
# The actual maximalization map on marked enriched diagrams

Maximalization retains every original simplicial set and map and marks
all its edges. Whole maximal-parameter prisms therefore give a genuine
enriched functor. The original identity underlying maps give a full
natural transformation to that diagram. No weak-equivalence or model
compatibility is asserted for maximalization.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace SSet.Marked

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every whole marked prism maximalizes by the same original underlying simplicial map. -/
def maximalizationMapping (X Y : Marked.{u}) :
    mappingComplex .maximal X Y ⟶ mappingComplex .maximal (max X.toSSet) (max Y.toSSet) where
  app n := ↾fun f => toMax f.hom
  naturality n m f := by
    ext p
    apply Hom.ext
    rfl

/-- Maximalization is a genuine enriched functor retaining all original objects and whole Hom maps. -/
def maximalizationEnriched : EnrichedFunctor SSet.{u} Marked.{u} Marked.{u} where
  obj X := max X.toSSet
  map := maximalizationMapping
  map_id X := by
    ext n z
    apply Hom.ext
    rfl
  map_comp X Y Z := by
    ext n fg
    apply Hom.ext
    rfl

/-- The original full marked enriched diagram maximalizes by the same whole underlying maps. -/
def maximalizedDiagram {C : Type v} [EnrichedCategory SSet.{u} C] (F : EnrichedDiagram C) : EnrichedDiagram C :=
  F.comp SSet.{u} maximalizationEnriched

/-- The identity original underlying maps give a genuine whole enriched natural maximalization map. -/
def diagramMaximalization {C : Type v} [EnrichedCategory SSet.{u} C] (F : EnrichedDiagram C) :
    F ⟶ maximalizedDiagram F where
  app x := toMax (𝟙 (F.obj x).toSSet)
  naturality x y := by
    ext n h
    apply Hom.ext
    rfl

/-- The actual maximalization component keeps precisely the entire original underlying identity. -/
theorem diagramMaximalization_hom {C : Type v} [EnrichedCategory SSet.{u} C]
    (F : EnrichedDiagram C) (x : C) : ((diagramMaximalization F).app x).hom = 𝟙 (F.obj x).toSSet := rfl

end SSet.Marked
