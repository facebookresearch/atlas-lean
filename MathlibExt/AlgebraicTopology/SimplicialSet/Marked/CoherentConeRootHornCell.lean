/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootValueIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootCoordinateScalarFreeCells

/-!
# The actual original entire root-horn free cell

The SAME original root-horn coefficient inclusion is a genuine
coefficient trivial cofibration. Its original free extension at the
unchanged thickened root has the actual full weak-mono projective left
class. The original identity unit enters the SAME supported horn diagram
and gives its full original enriched attaching square.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq
  coefficientMarkedModelCategory

/-- The SAME original supported root coefficient inclusion is a genuine coefficient trivial cofibration through its
exact original root-coefficient isomorphism. -/
theorem coneRootHornInclusion_root_trivialCofibration {n : ℕ} (k : Fin (n + 2)) (hk : 0 < k)
    (hk' : k < Fin.last (n + 1)) :
    trivialCofibrations Marked.{u} (coneRootHornInclusion k (⊥ : Vertex.{u} (n + 1))) := by
  let e : Arrow.mk (coneRootHornInclusion k (⊥ : Vertex.{u} (n + 1))) ≅
      Arrow.mk (coneRootCoordinateHornMap k) :=
    Arrow.isoMk (coneRootHornRootIso k) (Iso.refl _)
      ((coneRootHornRootIso_inclusion k).trans (Category.comp_id _).symm)
  exact ((trivialCofibrations Marked.{u}).arrow_mk_iso_iff e).mpr
    (coneRootCoordinateHorn_trivialCofibration k hk hk')

/-- The complete original horn coefficient is freed at the SAME original thickened root, retaining its whole
original source, target and coefficient map. -/
def coneRootHornCellFreeMap {n : ℕ} (k : Fin (n + 2)) :
    enrichedFreeDiagram (Index.{u} (n + 1))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
        (coneRootHornMarked k (⊥ : Vertex.{u} (n + 1))) ⟶
      enrichedFreeDiagram (Index.{u} (n + 1))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
        (coneWeight (⊥ : Vertex.{u} (n + 1))) :=
  (enrichedFreeDiagramFunctor (Index.{u} (n + 1))ᵒᵖ
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))).map
      (coneRootHornInclusion k (⊥ : Vertex.{u} (n + 1)))

/-- The actual original root-horn free map has the full genuine coefficient weak-mono projective left class, by the
original free/evaluation adjunction and actual coefficient WFS. -/
theorem coneRootHornCellFreeMap_projectiveWeakLeft {n : ℕ} (k : Fin (n + 2)) (hk : 0 < k)
    (hk' : k < Fin.last (n + 1)) :
    (enrichedFreeGenerators (Index.{u} (n + 1))ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      (coneRootHornCellFreeMap k) := by
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))
  let f := coneRootHornInclusion k (⊥ : Vertex.{u} (n + 1))
  have hleft : coefficientGeneratingWeakMonos.rlp.llp f := by
    rw [coefficientGeneratingWeakMonos_rlp, fibrations_llp]
    exact coneRootHornInclusion_root_trivialCofibration k hk hk'
  intro F G p hp
  exact (Adjunction.hasLiftingProperty_iff (enrichedFreeEvaluationAdjunction (Index.{u} (n + 1))ᵒᵖ c) f p).mpr
    (hleft (p.app c)
      ((enrichedFreeGenerators_rlp_iff (Index.{u} (n + 1))ᵒᵖ coefficientGeneratingWeakMonos p).mp hp c))

/-- The SAME original entire supported horn coefficient extends by its actual identity unit into the whole original
supported enriched diagram. -/
def coneRootHornFreeLeg {n : ℕ} (k : Fin (n + 2)) :
    enrichedFreeDiagram (Index.{u} (n + 1))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
      (coneRootHornMarked k (⊥ : Vertex.{u} (n + 1))) ⟶ coneRootHornDiagram k :=
  enrichedFreeExtend (Index.{u} (n + 1))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
    (coneRootHornMarked k (⊥ : Vertex.{u} (n + 1))) (coneRootHornDiagram k) (𝟙 _)

/-- The full original free-root horn leg retains precisely its SAME original whole coefficient identity under actual
native unit evaluation. -/
theorem coneRootHornFreeLeg_unit {n : ℕ} (k : Fin (n + 2)) :
    enrichedFreeUnit (Index.{u} (n + 1))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
        (coneRootHornMarked k (⊥ : Vertex.{u} (n + 1))) ≫
      (coneRootHornFreeLeg k).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))) = 𝟙 _ :=
  enrichedFreeExtend_unit (Index.{u} (n + 1))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
    (coneRootHornMarked k (⊥ : Vertex.{u} (n + 1))) (coneRootHornDiagram k) (𝟙 _)

/-- The SAME original entire root-horn free-cell square commutes as a full original marked enriched square, with
both original whole attaching maps. -/
theorem coneRootHornCell_condition {n : ℕ} (k : Fin (n + 2)) :
    coneRootHornCellFreeMap.{u} k ≫ coneRootFreeMap (n + 1) =
      coneRootHornFreeLeg k ≫ coneRootHornDiagramInclusion k := by
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))
  let A := coneRootHornMarked k (⊥ : Vertex.{u} (n + 1))
  apply (enrichedFreeHomEquiv (Index.{u} (n + 1))ᵒᵖ c A (coneDiagram (n + 1))).injective
  have hl := (enrichedFreeEvaluationAdjunction (Index.{u} (n + 1))ᵒᵖ c).homEquiv_naturality_left
    (coneRootHornInclusion k (⊥ : Vertex.{u} (n + 1))) (coneRootFreeMap (n + 1))
  have hr := (enrichedFreeEvaluationAdjunction (Index.{u} (n + 1))ᵒᵖ c).homEquiv_naturality_right
    (coneRootHornFreeLeg k) (coneRootHornDiagramInclusion k)
  change enrichedFreeUnit _ c A ≫ (coneRootHornCellFreeMap k ≫ coneRootFreeMap (n + 1)).app c =
    coneRootHornInclusion k (⊥ : Vertex.{u} (n + 1)) ≫
      (enrichedFreeUnit _ c (coneWeight (⊥ : Vertex.{u} (n + 1))) ≫ (coneRootFreeMap (n + 1)).app c) at hl
  change enrichedFreeUnit _ c A ≫ (coneRootHornFreeLeg k ≫ coneRootHornDiagramInclusion k).app c =
    (enrichedFreeUnit _ c A ≫ (coneRootHornFreeLeg k).app c) ≫
      coneRootHornInclusion k (⊥ : Vertex.{u} (n + 1)) at hr
  rw [coneRootFreeMap_unit] at hl
  rw [coneRootHornFreeLeg_unit] at hr
  exact hl.trans ((Category.comp_id _).trans ((Category.id_comp _).symm.trans hr.symm))

end SSet.Marked.CoherentWeight
