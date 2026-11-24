/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.ClusterAlgebra.Mutation
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp

/-!
# Tests for matrix and seed mutation
-/

namespace MathlibExtTest.RingTheory.ClusterAlgebra.Mutation

open MathlibExt.RingTheory.ClusterAlgebra

/-- Mutating the `A₂` exchange matrix flips its sign. -/
example : matrixMutation (0 : Fin 2) !![0, 1; -1, 0] = !![0, -1; 1, 0] := by decide

/-- A rank-three mutation that changes an entry away from row and column `k`: in the
quiver `1 → 0 → 2`, mutation at `0` creates the arrow `1 → 2`. -/
example : matrixMutation (0 : Fin 3) !![0, -1, 1; 1, 0, 0; -1, 0, 0] =
    !![0, 1, -1; -1, 0, 1; 1, -1, 0] := by decide

example : matrixMutation (0 : Fin 3) (matrixMutation 0 !![0, -1, 1; 1, 0, 0; -1, 0, 0]) =
    !![0, -1, 1; 1, 0, 0; -1, 0, 0] := matrixMutation_matrixMutation _ _

/-- The `A₂` exchange matrix is skew-symmetrizable (with `d = 1`). -/
example : IsSkewSymmetrizable !![(0 : ℤ), 1; -1, 0] :=
  ⟨fun _ => 1, fun _ => one_pos, by decide⟩

/-- The first seed mutation of type `A₂` gives `x₀' = (1 + x₁) / x₀`, the exchange relation
`x₀ x₀' = x₁ + 1` of the rank-two recurrence. -/
example (x y : ℚ) :
    (seedMutation (0 : Fin 2) (![x, y], !![0, 1; -1, 0])).1 0 = (1 + y) / x := by
  simp [seedMutation, Fin.prod_univ_two]

end MathlibExtTest.RingTheory.ClusterAlgebra.Mutation
