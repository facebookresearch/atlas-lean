/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathOperatorComposition
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance

/-!
# The actual Segal path fibre operator is weak when its original transition edge is invertible

The whole original operator triangle proves its fibre transition is
homotopic to postcomposition by the same actual initial edge. The
existing original equivalence-edge theorem makes that postcomposition
weak. Both whole row-point mapping comparisons are already weak, so
the actual original path fibre operator is weak by two-out-of-three.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

open SimplicialSpace.SegalHomotopy

/-- The original operator edge as its actual chosen mapping-fibre vertex. -/
def operatorEdgePoint {m n : ℕ} (W : SimplicialSpace.{u})
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :=
  SSet.yonedaEquiv (operatorEdgeFibreMap W f b)

set_option backward.isDefEq.respectTransparency false in
/-- The original short-edge composite is precisely postcomposition by the actual original operator edge. -/
theorem operatorShortEdges_postcomposition {m n : ℕ} (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    operatorShortEdges W x f b ≫ mappingComposition W hW x (tailFirstPoint W n b)
        (tailFirstPoint W m (b ≫ W.diagram.map f.op)) =
      rowPointMappingComparison W x n b ≫ mappingPostcomposition W hW x (tailFirstPoint W n b)
        (tailFirstPoint W m (b ≫ W.diagram.map f.op)) (operatorEdgePoint W f b) := by
  unfold mappingPostcomposition
  rw [← Category.assoc]
  apply congrArg (fun q => q ≫ mappingComposition W hW x (tailFirstPoint W n b)
    (tailFirstPoint W m (b ≫ W.diagram.map f.op)))
  apply prod.hom_ext
  · simp only [operatorShortEdges, Category.assoc, prod.lift_fst, Category.comp_id]
  · simp only [operatorShortEdges, Category.assoc, prod.lift_snd, operatorEdgePoint, Equiv.symm_apply_apply]
    rw [← Category.assoc, rowPointMappingComparison_snd]

/-- The actual original path fibre operator is weak when its same original operator edge is an equivalence. -/
theorem rowPointOperator_weak {m n : ℕ} (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌)
    (he : IsEquivalenceEdge W hW (operatorTailEdge W f b)) :
    SSet.realizationWeakEquivalences (rowPointOperator W x f b) := by
  have he' : IsEquivalenceEdge W hW
      ((mappingFibre.fst W (tailFirstPoint W n b)
        (tailFirstPoint W m (b ≫ W.diagram.map f.op))).app (op (SimplexCategory.mk 0))
        (operatorEdgePoint W f b)) := by
    have hp := congrArg SSet.yonedaEquiv (operatorEdgeFibreMap_fst W f b)
    simp only [SSet.yonedaEquiv_comp] at hp
    change (mappingFibre.fst W (tailFirstPoint W n b)
        (tailFirstPoint W m (b ≫ W.diagram.map f.op))).app (op (SimplexCategory.mk 0))
        (operatorEdgePoint W f b) = operatorTailEdge W f b at hp
    rw [hp]
    exact he
  have hp := mappingPostcomposition_realizationWeakEquivalence W hW
    (tailFirstPoint W n b) (tailFirstPoint W m (b ≫ W.diagram.map f.op))
    (operatorEdgePoint W f b) he' x
  have hc := SSet.realizationWeakEquivalences.comp_mem _ _ (rowPointMappingComparison_weak W hW x n b) hp
  have H := rowPointOperatorCompositionHomotopy W hW x f b
  rw [operatorShortEdges_postcomposition] at H
  have ht : SSet.realizationWeakEquivalences
      (rowPointOperator W x f b ≫ rowPointMappingComparison W x m (b ≫ W.diagram.map f.op)) :=
    (SSet.realizationWeakEquivalences_iff_of_homotopy H).mpr hc
  exact SSet.realizationWeakEquivalences.of_postcomp _ _
    (rowPointMappingComparison_weak W hW x m (b ≫ W.diagram.map f.op)) ht

end SimplicialSpace.LeftDecalageObject
