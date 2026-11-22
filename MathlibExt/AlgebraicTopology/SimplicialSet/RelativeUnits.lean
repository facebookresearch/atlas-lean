/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
# The whole original double-unit simplices

These three-simplices are actual double degeneracies of the original edge.
Their four faces retain the left or right unit triangles and the original
identity triangle. They supply prescribed base simplices for relative
association and cancellation, without choosing a base horn filler.
-/

universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Edge

variable {X : SSet.{u}} {x y : X _⦋0⦌} (e : Edge x y)

/-- The original three-simplex with two left units before this edge. -/
def leftUnitThree : X _⦋3⦌ := X.σ 0 (X.σ 0 e.edge)

/-- The original three-simplex with two right units after this edge. -/
def rightUnitThree : X _⦋3⦌ := X.σ 1 (X.σ 1 e.edge)

/-- Its zeroth face is the same original left-unit triangle. -/
theorem leftUnitThree_δ_zero : X.δ (0 : Fin 4) e.leftUnitThree = X.σ 0 e.edge :=
  δ_comp_σ_self_apply (S := X) (0 : Fin 3) (X.σ 0 e.edge)

/-- Its first face is that same left unit. -/
theorem leftUnitThree_δ_one : X.δ (1 : Fin 4) e.leftUnitThree = X.σ 0 e.edge :=
  δ_comp_σ_succ_apply (S := X) (0 : Fin 3) (X.σ 0 e.edge)

/-- Its second face is also the original left unit. -/
theorem leftUnitThree_δ_two : X.δ (2 : Fin 4) e.leftUnitThree = X.σ 0 e.edge := by
  have h := δ_comp_σ_of_gt'_apply (S := X) (i := (2 : Fin 4)) (j := (0 : Fin 3))
    (by decide) (X.σ 0 e.edge)
  have h' := δ_comp_σ_succ_apply (S := X) (0 : Fin 2) e.edge
  exact h.trans (congrArg (X.σ (0 : Fin 2)) h')

/-- Its last face is the original identity triangle at the source vertex. -/
theorem leftUnitThree_δ_three : X.δ (3 : Fin 4) e.leftUnitThree =
    X.σ 0 (X.σ 0 x) := by
  have h := δ_comp_σ_of_gt'_apply (S := X) (i := (3 : Fin 4)) (j := (0 : Fin 3))
    (by decide) (X.σ 0 e.edge)
  have h' := δ_comp_σ_of_gt'_apply (S := X) (i := (2 : Fin 3)) (j := (0 : Fin 2))
    (by decide) e.edge
  exact h.trans (congrArg (X.σ (0 : Fin 2))
    (h'.trans (congrArg (X.σ (0 : Fin 1)) e.src_eq)))

/-- The first included right-unit face is the original right unit. -/
theorem rightUnitThree_δ_one : X.δ (1 : Fin 4) e.rightUnitThree = X.σ 1 e.edge :=
  δ_comp_σ_self_apply (S := X) (1 : Fin 3) (X.σ 1 e.edge)

/-- The second right-unit face retains that same original triangle. -/
theorem rightUnitThree_δ_two : X.δ (2 : Fin 4) e.rightUnitThree = X.σ 1 e.edge :=
  δ_comp_σ_succ_apply (S := X) (1 : Fin 3) (X.σ 1 e.edge)

/-- The last face is also the original right unit. -/
theorem rightUnitThree_δ_three : X.δ (3 : Fin 4) e.rightUnitThree = X.σ 1 e.edge := by
  have h := δ_comp_σ_of_gt'_apply (S := X) (i := (3 : Fin 4)) (j := (1 : Fin 3))
    (by decide) (X.σ 1 e.edge)
  have h' := δ_comp_σ_succ_apply (S := X) (1 : Fin 2) e.edge
  exact h.trans (congrArg (X.σ (1 : Fin 2)) h')

/-- The zeroth face is the original identity triangle at the target vertex. -/
theorem rightUnitThree_δ_zero : X.δ (0 : Fin 4) e.rightUnitThree =
    X.σ 0 (X.σ 0 y) := by
  have h := δ_comp_σ_of_le_apply (S := X) (i := (0 : Fin 3)) (j := (0 : Fin 2))
    (by decide) (X.σ 1 e.edge)
  have h' := δ_comp_σ_of_le_apply (S := X) (i := (0 : Fin 2)) (j := (0 : Fin 1))
    (by decide) e.edge
  exact h.trans (congrArg (X.σ (0 : Fin 2))
    (h'.trans (congrArg (X.σ (0 : Fin 1)) e.tgt_eq)))

end SSet.Edge
