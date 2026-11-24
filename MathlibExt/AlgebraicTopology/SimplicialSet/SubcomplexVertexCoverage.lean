/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex

/-!
# Original vertex coverage rules out zero-dimensional relative cells

If all original vertices lie in a subcomplex, every original
nondegenerate simplex outside it has positive dimension. The actual
relative-simplex dimension and original vertex are retained.
-/

universe u
open scoped Simplicial

namespace SSet.Subcomplex

/-- Full original vertex coverage excludes zero-dimensional simplices from the native relative
  nondegenerate index. -/
theorem N.one_le_dim_of_vertices {X : SSet.{u}} {A : X.Subcomplex}
    (hA : ∀ x : X _⦋0⦌, x ∈ A.obj (Opposite.op ⦋0⦌)) (s : A.N) : 1 ≤ s.dim := by
  obtain ⟨n, x, hx, hx', rfl⟩ := N.mk_surjective s
  cases n with
  | zero => exact False.elim (hx' (hA x))
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)

end SSet.Subcomplex
