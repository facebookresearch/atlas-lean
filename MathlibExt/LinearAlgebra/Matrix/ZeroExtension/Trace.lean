/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.Matrix.ZeroExtension
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! The added zero diagonal entries do not change the actual finite matrix trace. -/

@[expose] public section

open scoped BigOperators

namespace Matrix

universe v

variable {A : Type v} [AddCommMonoid A]

/-- The true top-left zero extension preserves trace, including the empty source matrix. -/
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
