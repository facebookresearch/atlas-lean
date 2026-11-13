/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

/-!
# Integral basic feasible points

For the finite real inequality system `A *ᵥ x ≤ b`, `0 ≤ x`, a basic
feasible point of a totally unimodular system with integer bounds is integral.
The selected tight constraints may include the nonnegativity rows `-I`.
This does not assert that every feasible or optimal point is integral.
-/

public section

namespace Matrix

/-- A basic feasible point of `A *ᵥ x ≤ b`, `0 ≤ x` is integral when `A` is
 totally unimodular and `b` is integral. The basis selects rows from `[A; -I]`,
 with right-hand side `[b; 0]`, so nonnegativity constraints are selectable.

Feasibility records the LP context; the algebraic integrality argument uses
only the nonsingular tight basis. No objective or positive dimension is
needed. -/
theorem IsTotallyUnimodular.exists_int_vec_of_basic_feasible {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (hA : A.IsTotallyUnimodular)
    (b : Fin m → ℤ) {x : Fin n → ℝ}
    (_hx : ∀ j, 0 ≤ x j) (_hAx : ∀ i, (A *ᵥ x) i ≤ (b i : ℝ))
    (rows : Fin n → Fin m ⊕ Fin n)
    (hdet : ((fromRows A (-1)).submatrix rows id).det ≠ 0)
    (htight : ((fromRows A (-1)).submatrix rows id) *ᵥ x =
      fun i => ((Sum.elim b (fun _ => 0) (rows i) : ℤ) : ℝ)) :
    ∃ z : Fin n → ℤ, ∀ i, (z i : ℝ) = x i := by
  have haug :
      (fromRows A (-1 : Matrix (Fin n) (Fin n) ℝ)).IsTotallyUnimodular := by
    apply hA.fromRows_unitlike
    intro _ i
    refine ⟨i, -1, ?_⟩
    ext j
    simp [one_apply, Pi.single_apply, eq_comm]
    split_ifs <;> simp
  exact (haug.submatrix rows id).exists_int_vec hdet
    (fun i => Sum.elim b (fun _ => 0) (rows i)) htight

end Matrix
