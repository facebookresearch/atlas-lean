/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialEdgeSourceWeak
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialEdgeSourceTarget

/-!
# The genuine original fixed-object Segal path row comparison

The actual whole original fixed-object row maps to the original
source-edge family over the first vertex of its entire tail simplex.
Its complete comparison is weak from the original interval-cover
restriction and sharp source base change. All original point, edge
and tail projection legs are retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The actual whole original fixed-object row retains the original leading edge and entire tail simplex. -/
def leadingEdgeComparison (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    (diagram W x).obj (op (SimplexCategory.mk n)) ⟶
      InitialEdgeTailMapping.sourceEdgeTarget W x n :=
  (rowIso W x n).hom ≫ InitialEdgeTailMapping.sourceFibreComparison W x n ≫
    (InitialEdgeTailMapping.sourceEdgeTargetIso W x n).hom

/-- The complete original leading-edge comparison is genuinely weak at an original Segal space. -/
theorem leadingEdgeComparison_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    SSet.realizationWeakEquivalences (leadingEdgeComparison W x n) :=
  SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso (rowIso W x n).hom)
    (SSet.realizationWeakEquivalences.comp_mem _ _
      (InitialEdgeTailMapping.sourceFibreComparison_weak W hW x n)
      (SSet.realizationWeakEquivalences.of_isIso (InitialEdgeTailMapping.sourceEdgeTargetIso W x n).hom))

set_option backward.isDefEq.respectTransparency false in
/-- The complete original leading-edge comparison retains the same whole tail projection. -/
theorem leadingEdgeComparison_tail (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    leadingEdgeComparison W x n ≫ pullback.snd _ _ =
      (projection W x).app (op (SimplexCategory.mk n)) := by
  rw [leadingEdgeComparison, Category.assoc, Category.assoc,
    InitialEdgeTailMapping.sourceEdgeTargetIso_tail]
  rw [← Category.assoc (InitialEdgeTailMapping.sourceFibreComparison W x n),
    InitialEdgeTailMapping.sourceFibreComparison_fst]
  simp only [Category.assoc]
  rw [InitialEdgeTailMapping.rowComparison_fst, ← Category.assoc, rowIso_fst]
  change (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
      W.diagram.map (SimplexCategory.δ (0 : Fin (n + 2))).op =
    (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
      W.diagram.map (SimplicialObject.LeftDecalage.rightBlock.app (SimplexCategory.mk n)).op
  rw [SimplicialObject.LeftDecalage.rightBlock_delta]

set_option backward.isDefEq.respectTransparency false in
/-- The complete original leading-edge comparison retains its whole original leading edge. -/
theorem leadingEdgeComparison_edge (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    leadingEdgeComparison W x n ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
        W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin (n + 1))).op := by
  rw [leadingEdgeComparison]
  simp only [Category.assoc]
  rw [InitialEdgeTailMapping.sourceEdgeTargetIso_edge]
  rw [← Category.assoc (InitialEdgeTailMapping.sourceFibreComparison W x n),
    InitialEdgeTailMapping.sourceFibreComparison_fst]
  simp only [Category.assoc]
  rw [InitialEdgeTailMapping.rowComparison_snd, ← Category.assoc, rowIso_fst]

end SimplicialSpace.LeftDecalageObject
