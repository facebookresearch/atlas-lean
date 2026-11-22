/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailVertices
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterFreeSpan

/-!
# The positive-cone free relations indexed by original smaller vertices

The actual zeroth coface indexes every positive target vertex by its
original smaller vertex. The free coefficients and full path
relations use exactly those original images. Their cocone is the
original positive-cone cocone, with no replacement of its marked data.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Original smaller vertices index the actual positive target free coefficients and whole path relations. -/
def coneTailFreeSpan (n : ℕ) :
    MultispanIndex (.ofLinearOrder (Vertex.{u} n)) (EnrichedDiagram (Index.{u} (n + 1))ᵒᵖ) :=
  coneVertexFreeSpan (coneTailEmbedding n).toOrderHom

/-- The actual original free tail coefficient enters the genuine positive cone by its original bound insertion. -/
def coneTailFreeLeg (n : ℕ) (j : Vertex.{u} n) :
    (coneTailFreeSpan n).right j ⟶ coneAfterDiagram (⊥ : Vertex.{u} (n + 1)) :=
  coneAfterFreeLeg (⊥ : Vertex.{u} (n + 1)) (coneTailVertexOrderIso n j)

/-- Every original free tail leg keeps the full actual path action and original upper coefficient. -/
theorem coneTailFreeLeg_app (n : ℕ) (i : Vertex.{u} (n + 1)) (j : Vertex.{u} n) :
    (coneTailFreeLeg n j).app (op (SimplicialThickening.mk i)) =
      prodMap (𝟙 (max (nerve (SimplicialThickening.Path i (coneTailEmbedding n j)))))
        (coneAfterAboveIso (coneTailEmbedding_positive j)).inv ≫
      coneAfterAction i (coneTailEmbedding n j) (⊥ : Vertex.{u} (n + 1)) :=
  coneAfterFreeLeg_app i (⊥ : Vertex.{u} (n + 1)) (coneTailVertexOrderIso n j)

/-- Every ordered original path relation agrees through the same original positive-cone legs. -/
theorem coneTailFreeSpan_condition (n : ℕ) (p : (MultispanShape.ofLinearOrder (Vertex.{u} n)).L) :
    (coneTailFreeSpan n).fst p ≫ coneTailFreeLeg n p.val.1 =
      (coneTailFreeSpan n).snd p ≫ coneTailFreeLeg n p.val.2 :=
  coneAfterFreeSpan_condition (⊥ : Vertex.{u} (n + 1))
    ⟨(coneTailVertexOrderIso n p.val.1, coneTailVertexOrderIso n p.val.2),
      (coneTailVertexOrderIso n).strictMono p.property⟩

/-- The original smaller ordinal indexes the genuine full positive-cone free cocone. -/
def coneTailFreeCocone (n : ℕ) : Multicofork (coneTailFreeSpan.{u} n) :=
  Multicofork.ofπ _ (coneAfterDiagram (⊥ : Vertex.{u} (n + 1))) (coneTailFreeLeg n)
    (coneTailFreeSpan_condition n)

end SSet.Marked.CoherentWeight
