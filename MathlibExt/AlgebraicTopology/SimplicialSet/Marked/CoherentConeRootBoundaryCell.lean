/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootValueIso

/-!
# The actual complete root-boundary free cell

The original coordinate boundary at the root enters the original full
root coefficient by its unchanged marked inclusion. Its free extension
enters the actual supported enriched diagram by the native identity
unit. The resulting square commutes on the whole original enriched
diagram, rather than only on selected vertices or scalar degrees.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Every actual supported coefficient enters its original whole cone monically. -/
instance {n : ℕ} (i : Vertex.{u} n) : Mono (coneRootBoundaryInclusion i) :=
  (mono_iff_underlying _).mpr (inferInstance : Mono (coneRootBoundarySupport i).ι)

/-- The actual root support is the original complete coordinate boundary with its inherited marking. -/
def coneRootBoundaryRootIso (n : ℕ) :
    coneRootBoundaryMarked (⊥ : Vertex.{u} n) ≅ coneCoordinateBoundaryMarked (⊥ : Vertex.{u} n) :=
  isoMk (Subcomplex.eqToIso (coneRootBoundarySupport_root n)) (fun _ => Iff.rfl)

/-- The original coordinate-boundary chart retains the exact inclusion in the full cone. -/
theorem coneRootBoundaryRootIso_inclusion (n : ℕ) :
    (coneRootBoundaryRootIso.{u} n).hom ≫ coneCoordinateBoundaryMap (⊥ : Vertex.{u} n) =
      coneRootBoundaryInclusion (⊥ : Vertex.{u} n) := by
  apply Hom.ext
  rfl

/-- The full original root boundary has its actual free marked coefficient inclusion. -/
def coneRootBoundaryCellFreeMap (n : ℕ) :
    enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
        (coneRootBoundaryMarked (⊥ : Vertex.{u} n)) ⟶
      enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
        (coneWeight (⊥ : Vertex.{u} n)) :=
  (enrichedFreeDiagramFunctor (Index.{u} n)ᵒᵖ
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))).map
      (coneRootBoundaryInclusion (⊥ : Vertex.{u} n))

/-- The whole original boundary root coefficient extends by its actual identity into the same supported diagram. -/
def coneRootBoundaryFreeLeg (n : ℕ) :
    enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
      (coneRootBoundaryMarked (⊥ : Vertex.{u} n)) ⟶ coneRootBoundaryDiagram n :=
  enrichedFreeExtend _ _ _ _ (𝟙 _)

/-- The unchanged full coordinate-boundary free map has the actual projective left class. -/
theorem coneRootBoundaryCellFreeMap_projectiveLeft (n : ℕ) :
    (enrichedFreeGenerators (Index.{u} n)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      (coneRootBoundaryCellFreeMap.{u} n) :=
  enrichedFree_markedMono_left (Index.{u} n)ᵒᵖ
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
      (coneRootBoundaryInclusion (⊥ : Vertex.{u} n))

/-- Original native unit evaluation of the complete root-boundary extension is the same full boundary coefficient
identity. -/
theorem coneRootBoundaryFreeLeg_unit (n : ℕ) :
    enrichedFreeUnit (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
        (coneRootBoundaryMarked (⊥ : Vertex.{u} n)) ≫
      (coneRootBoundaryFreeLeg n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) = 𝟙 _ :=
  enrichedFreeExtend_unit (Index.{u} n)ᵒᵖ
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
      (coneRootBoundaryMarked (⊥ : Vertex.{u} n)) (coneRootBoundaryDiagram n) (𝟙 _)

/-- The actual complete root-boundary square commutes as a whole enriched marked square. -/
theorem coneRootBoundaryCell_condition (n : ℕ) :
    coneRootBoundaryCellFreeMap.{u} n ≫ coneRootFreeMap n =
      coneRootBoundaryFreeLeg n ≫ coneRootBoundaryDiagramInclusion n := by
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} n))
  let A := coneRootBoundaryMarked (⊥ : Vertex.{u} n)
  apply (enrichedFreeHomEquiv (Index.{u} n)ᵒᵖ c A (coneDiagram n)).injective
  have hl := (enrichedFreeEvaluationAdjunction (Index.{u} n)ᵒᵖ c).homEquiv_naturality_left
    (coneRootBoundaryInclusion (⊥ : Vertex.{u} n)) (coneRootFreeMap n)
  have hr := (enrichedFreeEvaluationAdjunction (Index.{u} n)ᵒᵖ c).homEquiv_naturality_right
    (coneRootBoundaryFreeLeg n) (coneRootBoundaryDiagramInclusion n)
  change enrichedFreeUnit _ c A ≫ (coneRootBoundaryCellFreeMap n ≫ coneRootFreeMap n).app c =
    coneRootBoundaryInclusion (⊥ : Vertex.{u} n) ≫
      (enrichedFreeUnit _ c (coneWeight (⊥ : Vertex.{u} n)) ≫ (coneRootFreeMap n).app c) at hl
  change enrichedFreeUnit _ c A ≫
      (coneRootBoundaryFreeLeg n ≫ coneRootBoundaryDiagramInclusion n).app c =
    (enrichedFreeUnit _ c A ≫ (coneRootBoundaryFreeLeg n).app c) ≫
      coneRootBoundaryInclusion (⊥ : Vertex.{u} n) at hr
  rw [coneRootFreeMap_unit] at hl
  rw [coneRootBoundaryFreeLeg_unit] at hr
  exact hl.trans ((Category.comp_id _).trans ((Category.id_comp _).symm.trans hr.symm))

end SSet.Marked.CoherentWeight
