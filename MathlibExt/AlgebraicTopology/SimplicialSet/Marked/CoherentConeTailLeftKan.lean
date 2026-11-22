/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanAdjunction

/-!
# The actual original tail left-extension comparison map

The whole native coface operator has its actual left-extension mate
into the original positive cone. Its unit components retain the same
original coface image maps. Composing with the original positive-cone
inclusion is exactly the original full cone-operator mate.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original whole tail operator has its actual universal left-extension mate into the same positive cone. -/
def coneTailLeftKanMap (n : ℕ) :
    EnrichedLeftKan.object (coneTailIndex n) (coneDiagram n) ⟶
      coneAfterDiagram (⊥ : Vertex.{u} (n + 1)) :=
  (EnrichedLeftKan.universalHomEquiv (coneTailIndex n) (coneDiagram n)
    (coneAfterDiagram (⊥ : Vertex.{u} (n + 1)))).symm (coneTailOperator n)

/-- The actual original left-extension unit followed by the tail mate is precisely the whole original tail operator. -/
theorem coneTailLeftKanMap_unit (n : ℕ) :
    EnrichedLeftKan.unit (coneTailIndex.{u} n) (coneDiagram n) ≫
      (enrichedDiagramRestrict (coneTailIndex n)).map (coneTailLeftKanMap n) = coneTailOperator n :=
  (EnrichedLeftKan.universalHomEquiv_unit (coneTailIndex n) (coneDiagram n)
    (coneAfterDiagram (⊥ : Vertex.{u} (n + 1))) (coneTailLeftKanMap n)).symm.trans
    ((EnrichedLeftKan.universalHomEquiv (coneTailIndex n) (coneDiagram n)
      (coneAfterDiagram (⊥ : Vertex.{u} (n + 1)))).apply_symm_apply (coneTailOperator n))

/-- Every original unit component of the actual tail mate is its unchanged original marked coface coefficient map. -/
theorem coneTailLeftKanMap_unit_app (n : ℕ) (i : (Index.{u} n)ᵒᵖ) :
    (EnrichedLeftKan.unit (coneTailIndex n) (coneDiagram n)).app i ≫
      (coneTailLeftKanMap n).app ((coneTailIndex n).obj i) =
        (coneTailAfterCoefficientIso n i.unop.as).hom :=
  congrArg (fun f => f.app i) (coneTailLeftKanMap_unit n)

/-- The actual restricted positive-cone inclusion carries the same original tail operator to the whole
  original cone operator. -/
theorem coneTailOperator_inclusion (n : ℕ) :
    coneTailOperator n ≫ (enrichedDiagramRestrict (coneTailIndex n)).map
      (coneAfterDiagramInclusion (⊥ : Vertex.{u} (n + 1))) =
        coneOperator (coneTailEmbedding n).toOrderHom := by
  apply EnrichedDiagramMap.ext
  funext i
  exact coneTailAfterCoefficientIso_inclusion n i.unop.as

/-- The actual full original cone coface operator has its same native universal left-extension mate. -/
def coneTailLeftKanInclusion (n : ℕ) :
    EnrichedLeftKan.object (coneTailIndex n) (coneDiagram n) ⟶ coneDiagram (n + 1) :=
  (EnrichedLeftKan.universalHomEquiv (coneTailIndex n) (coneDiagram n) (coneDiagram (n + 1))).symm
    (coneOperator (coneTailEmbedding n).toOrderHom)

/-- The actual positive-tail comparison followed by its original inclusion is exactly the original full
  coface left-extension map. -/
theorem coneTailLeftKanMap_inclusion (n : ℕ) :
    coneTailLeftKanMap n ≫ coneAfterDiagramInclusion (⊥ : Vertex.{u} (n + 1)) = coneTailLeftKanInclusion n := by
  apply (EnrichedLeftKan.universalHomEquiv (coneTailIndex n) (coneDiagram n) (coneDiagram (n + 1))).injective
  have h := EnrichedLeftKan.universalHomEquiv_natural_right (coneTailIndex n) (coneDiagram n)
    (coneTailLeftKanMap n) (coneAfterDiagramInclusion (⊥ : Vertex.{u} (n + 1)))
  have ht := (EnrichedLeftKan.universalHomEquiv (coneTailIndex n) (coneDiagram n)
    (coneAfterDiagram (⊥ : Vertex.{u} (n + 1)))).apply_symm_apply (coneTailOperator n)
  exact h.trans
    ((congrArg (fun f => f ≫ (enrichedDiagramRestrict (coneTailIndex n)).map
        (coneAfterDiagramInclusion (⊥ : Vertex.{u} (n + 1)))) ht).trans
      ((coneTailOperator_inclusion n).trans
        ((EnrichedLeftKan.universalHomEquiv (coneTailIndex n) (coneDiagram n) (coneDiagram (n + 1))).apply_symm_apply
          (coneOperator (coneTailEmbedding n).toOrderHom)).symm))

end SSet.Marked.CoherentWeight
