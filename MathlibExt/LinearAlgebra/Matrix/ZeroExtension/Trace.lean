/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.Matrix.ZeroExtension
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace of a top-left zero extension

Let A be an additive commutative monoid and r≤s. Extending an r×r matrix to the top-left block
of an s×s matrix and setting every added entry to zero preserves the sum of diagonal entries.
Thus zero extension preserves trace, including r=0.
-/

@[expose] public section

open scoped BigOperators

namespace Matrix

universe v

variable {A : Type v} [AddCommMonoid A]

/-- For an additive commutative monoid A, natural numbers r≤s and B:Matrix(Fin r,Fin r,A),
trace(zeroExtend(B))=trace(B). The added diagonal entries are zero, and the equality includes
the empty source matrix r=0. -/
theorem zeroExtend_trace {r s : ℕ} (h : r ≤ s) (B : Matrix (Fin r) (Fin r) A) :
    Matrix.trace (zeroExtend h B) = Matrix.trace B := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  change (∑ i : Fin (r + d), zeroExtend h B i i) = ∑ i : Fin r, B i i
  rw [Fin.sum_trunc _ (by
    intro i
    apply zeroExtend_of_row h B
    exact Nat.le_add_right r i.val)]
  apply Finset.sum_congr rfl
  intro i _
  change zeroExtend h B (i.castLE h) (i.castLE h) = B i i
  exact zeroExtend_castLE h B i i

end Matrix
