/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverRankFiltration
import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveGeneratorCells
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidCoverParentEdgeData

/-!
# Full original native cover-parent simplex cells

Every original vertex of the supplied positive rank indexes its actual
original parent generator with its native orientation. Each simplex
retains all ordinal coefficients and individual original endpoints.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating quiver used by the actual native parent cells. -/
private local instance coverQuiverForCells : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- Every actual individual original vertex of the supplied positive rank. -/
abbrev CoverCellLabel (k : ℕ) := {a : CoverVertex V z // CoverVertex.rank V z a = k + 1}

/-- The SAME actual positive-rank hypothesis for an original cell label. -/
lemma coverCellLabel_pos (k : ℕ) (a : CoverCellLabel V z k) : 0 < CoverVertex.rank V z a.val := by
  rw [a.property]
  exact Nat.zero_lt_succ _

/-- The entire native simplex of the SAME original parent-generating arrow. -/
def coverParentCell (k : ℕ) (a : CoverCellLabel V z k) :
    (Δ[1] : SSet.{max u v}) ⟶ nerve (Paths (CoverVertex V z)) :=
  CategoryTheory.FreePathNerveCoordinates.generatorCell (CoverVertex V z)
    (parentEdgeArrow V z a.val (coverCellLabel_pos V z k a))

/-- EVERY coefficient of the original parent cell retains its SAME native generator word. -/
lemma coverParentCell_app (k : ℕ) (a : CoverCellLabel V z k) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) :
    (coverParentCell V z k a).app (op ⦋n⦌) c =
      (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv c)).toFunctor ⋙
        CategoryTheory.FreePathNerveCoordinates.generatorWord (CoverVertex V z)
          (parentEdgeArrow V z a.val (coverCellLabel_pos V z k a)) := rfl

/-- Every original parent cell lies in the SAME native full generating graph. -/
lemma coverParentCell_range_le_graph (k : ℕ) (a : CoverCellLabel V z k) :
    SSet.Subcomplex.range (coverParentCell V z k a) ≤ coverGraph V z :=
  CategoryTheory.FreePathNerveCoordinates.generatorCell_range_le (CoverVertex V z)
    (parentEdgeArrow V z a.val (coverCellLabel_pos V z k a))

/-- Every source coefficient keeps the SAME individual original source vertex. -/
lemma coverParentCell_obj_zero (k : ℕ) (a : CoverCellLabel V z k) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) (i : Fin (n + 1)) (h : c i = 0) :
    ((coverParentCell V z k a).app (op ⦋n⦌) c).obj i =
      parentEdgeSource V z a.val (coverCellLabel_pos V z k a) :=
  CategoryTheory.FreePathNerveCoordinates.generatorCell_obj_zero (CoverVertex V z)
    (parentEdgeArrow V z a.val (coverCellLabel_pos V z k a)) n c i h

/-- Every target coefficient keeps the SAME individual original target vertex. -/
lemma coverParentCell_obj_one (k : ℕ) (a : CoverCellLabel V z k) (n : ℕ)
    (c : (Δ[1] : SSet.{max u v}) _⦋n⦌) (i : Fin (n + 1)) (h : c i = 1) :
    ((coverParentCell V z k a).app (op ⦋n⦌) c).obj i =
      parentEdgeTarget V z a.val (coverCellLabel_pos V z k a) :=
  CategoryTheory.FreePathNerveCoordinates.generatorCell_obj_one (CoverVertex V z)
    (parentEdgeArrow V z a.val (coverCellLabel_pos V z k a)) n c i h

end Quiver.FreeGroupoid.OriginalWords
