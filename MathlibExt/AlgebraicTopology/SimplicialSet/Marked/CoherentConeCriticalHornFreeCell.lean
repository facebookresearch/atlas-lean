/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalHornDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootHornWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootValueIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootCoordinateScalarFreeCells

/-!
# The actual whole original critically marked free-root horn cell

The genuine original marked root-horn trivial cofibration retains its
whole critical coefficient and exact attaching map. Freeing it at the
same original thickened root gives its actual weak projective left
class. The two original coefficient identities extend into the same
full critical horn and cone, with their actual free/evaluation units
and complete original enriched attaching square.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq
  coefficientMarkedModelCategory

/-- The SAME entire supported critical root coefficient inclusion is genuinely trivial-cofibrant through its exact
original full marked root isomorphism. -/
theorem coneCriticalHornRootInclusion_trivialCofibration (n : ℕ) :
    trivialCofibrations Marked.{u} (coneCriticalHornCoefficientInclusion n (⊥ : Vertex.{u} (n + 2))) := by
  let e : Arrow.mk (coneCriticalHornCoefficientInclusion n (⊥ : Vertex.{u} (n + 2))) ≅ Arrow.mk
    (coneCriticalRootHornMap n) :=
    Arrow.isoMk (coneCriticalHornRootIso n) (Iso.refl _)
      ((coneCriticalHornRootIso_inclusion n).trans (Category.comp_id _).symm)
  exact ((trivialCofibrations Marked.{u}).arrow_mk_iso_iff e).mpr (coneCriticalRootHornMap_trivialCofibration n)

/-- The same whole original critically marked root-horn arrow is freed at its SAME original thickened root with both
original complete coefficients retained. -/
def coneCriticalHornCellFreeMap (n : ℕ) :
    enrichedFreeDiagram (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
        (coneCriticalHornWeight n (⊥ : Vertex.{u} (n + 2))) ⟶
      enrichedFreeDiagram (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
        (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))) :=
  (enrichedFreeDiagramFunctor (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))).map
    (coneCriticalHornCoefficientInclusion n (⊥ : Vertex.{u} (n + 2)))

/-- The same actual whole critically marked free-root map has its genuine full weak projective left class through
the original free/evaluation adjunction and coefficient WFS. -/
theorem coneCriticalHornCellFreeMap_projectiveWeakLeft (n : ℕ) :
    (enrichedFreeGenerators (Index.{u} (n + 2))ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      (coneCriticalHornCellFreeMap n) := by
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2)))
  let f := coneCriticalHornCoefficientInclusion n (⊥ : Vertex.{u} (n + 2))
  have hleft : coefficientGeneratingWeakMonos.rlp.llp f := by
    rw [coefficientGeneratingWeakMonos_rlp, fibrations_llp]
    exact coneCriticalHornRootInclusion_trivialCofibration n
  intro F G p hp
  exact (Adjunction.hasLiftingProperty_iff (enrichedFreeEvaluationAdjunction (Index.{u} (n + 2))ᵒᵖ c) f p).mpr
    (hleft (p.app c) ((enrichedFreeGenerators_rlp_iff (Index.{u} (n + 2))ᵒᵖ coefficientGeneratingWeakMonos p).mp hp c))

/-- The SAME complete original supported critical horn coefficient extends into its full enriched horn by its actual
original coefficient identity. -/
def coneCriticalHornFreeLeg (n : ℕ) :
    enrichedFreeDiagram (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
      (coneCriticalHornWeight n (⊥ : Vertex.{u} (n + 2))) ⟶ coneCriticalHornDiagram n :=
  enrichedFreeExtend (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
    (coneCriticalHornWeight n (⊥ : Vertex.{u} (n + 2))) (coneCriticalHornDiagram n) (𝟙 _)

/-- The SAME complete original critical target coefficient extends into its whole original cone by its actual
original coefficient identity. -/
def coneCriticalRootFreeLeg (n : ℕ) :
    enrichedFreeDiagram (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
      (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))) ⟶ coneCriticalDiagram n :=
  enrichedFreeExtend (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
    (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))) (coneCriticalDiagram n) (𝟙 _)

/-- The actual full original supported critical horn leg retains its exact coefficient identity under the genuine
free/evaluation unit. -/
theorem coneCriticalHornFreeLeg_unit (n : ℕ) :
    enrichedFreeUnit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
        (coneCriticalHornWeight n (⊥ : Vertex.{u} (n + 2))) ≫
      (coneCriticalHornFreeLeg n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2)))) = 𝟙 _ :=
  enrichedFreeExtend_unit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
    (coneCriticalHornWeight n (⊥ : Vertex.{u} (n + 2))) (coneCriticalHornDiagram n) (𝟙 _)

/-- The actual entire original critical target free leg retains its exact coefficient identity under the same
original free/evaluation unit. -/
theorem coneCriticalRootFreeLeg_unit (n : ℕ) :
    enrichedFreeUnit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
        (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))) ≫
      (coneCriticalRootFreeLeg n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2)))) = 𝟙 _ :=
  enrichedFreeExtend_unit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2))))
    (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))) (coneCriticalDiagram n) (𝟙 _)

/-- Both SAME complete original critically marked free-root maps form their actual full original enriched attaching
square. -/
theorem coneCriticalHornCell_condition (n : ℕ) :
    coneCriticalHornCellFreeMap.{u} n ≫ coneCriticalRootFreeLeg n = coneCriticalHornFreeLeg n ≫
      coneCriticalHornInclusion n := by
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2)))
  let A := coneCriticalHornWeight n (⊥ : Vertex.{u} (n + 2))
  apply (enrichedFreeHomEquiv (Index.{u} (n + 2))ᵒᵖ c A (coneCriticalDiagram n)).injective
  have hl := (enrichedFreeEvaluationAdjunction (Index.{u} (n + 2))ᵒᵖ c).homEquiv_naturality_left
    (coneCriticalHornCoefficientInclusion n (⊥ : Vertex.{u} (n + 2))) (coneCriticalRootFreeLeg n)
  have hr := (enrichedFreeEvaluationAdjunction (Index.{u} (n + 2))ᵒᵖ c).homEquiv_naturality_right
    (coneCriticalHornFreeLeg n) (coneCriticalHornInclusion n)
  change enrichedFreeUnit _ c A ≫ (coneCriticalHornCellFreeMap n ≫ coneCriticalRootFreeLeg n).app c =
    coneCriticalHornCoefficientInclusion n (⊥ : Vertex.{u} (n + 2)) ≫
      (enrichedFreeUnit _ c (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))) ≫ (coneCriticalRootFreeLeg n).app c) at hl
  change enrichedFreeUnit _ c A ≫ (coneCriticalHornFreeLeg n ≫ coneCriticalHornInclusion n).app c =
    (enrichedFreeUnit _ c A ≫ (coneCriticalHornFreeLeg n).app c) ≫ coneCriticalHornCoefficientInclusion n (⊥ :
      Vertex.{u} (n + 2)) at hr
  rw [coneCriticalRootFreeLeg_unit] at hl
  rw [coneCriticalHornFreeLeg_unit] at hr
  exact hl.trans ((Category.comp_id _).trans ((Category.id_comp _).symm.trans hr.symm))

end SSet.Marked.CoherentWeight
