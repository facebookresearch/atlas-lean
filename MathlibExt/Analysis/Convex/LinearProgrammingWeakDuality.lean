/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Weak linear programming duality

For primal-feasible `x` (`x ≥ 0`, `A *ᵥ x ≤ b`) and dual-feasible `y`
(`y ≥ 0`, `c ≤ Aᵀ *ᵥ y`), the primal objective is at most the dual
objective: `c ⬝ᵥ x ≤ b ⬝ᵥ y`. In particular a primal-dual pair with
equal objectives is optimal for both.

This is the lemma every LP consumer uses (certificate checking,
Farkas, zero-sum games). Strong duality
(`MathlibExt.Analysis.Convex.LPDuality.strong_linear_programming_duality`)
proves the same calculation as an internal `have`; this file exposes
it as a named theorem, with no change of proof.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.LPWeakDuality

open scoped Matrix

/-- Weak LP duality: any primal-feasible `x` and dual-feasible `y`
satisfy `c ⬝ᵥ x ≤ b ⬝ᵥ y`. -/
theorem weak_linear_programming_duality {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hAx : ∀ j, (A.mulVec x) j ≤ b j)
    {y : Fin m → ℝ} (hy : ∀ j, 0 ≤ y j)
    (hAty : ∀ i, c i ≤ (Aᵀ.mulVec y) i) :
    c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  calc c ⬝ᵥ x ≤ (Aᵀ.mulVec y) ⬝ᵥ x :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hAty i) (hx i)
    _ = x ⬝ᵥ (Aᵀ.mulVec y) := dotProduct_comm _ _
    _ = y ⬝ᵥ (A.mulVec x) := Matrix.dotProduct_transpose_mulVec A x y
    _ ≤ y ⬝ᵥ b :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hAx j) (hy j)
    _ = b ⬝ᵥ y := dotProduct_comm _ _

end MathlibExt.Analysis.Convex.LPWeakDuality
