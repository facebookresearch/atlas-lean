/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.FinitePythagoras
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Analysis.InnerProductSpace.FinitePythagoras

/-- The coordinate vectors `3 e₀` and `4 e₁` of the plane are orthogonal. -/
private theorem threeFour_orthogonal :
    Pairwise fun i j => inner ℝ
      ((![EuclideanSpace.single 0 3, EuclideanSpace.single 1 4] :
        Fin 2 → EuclideanSpace ℝ (Fin 2)) i)
      ((![EuclideanSpace.single 0 3, EuclideanSpace.single 1 4] :
        Fin 2 → EuclideanSpace ℝ (Fin 2)) j) = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [EuclideanSpace.inner_single_left]

/-- Pythagoras for `3 e₀` and `4 e₁`: the squared norm of their sum is `9 + 16 = 25`. -/
example : ‖(EuclideanSpace.single 0 3 + EuclideanSpace.single 1 4 :
    EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 25 := by
  have h := norm_sum_sq_eq_sum_norm_sq _ threeFour_orthogonal
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h, PiLp.norm_single, PiLp.norm_single]
  norm_num

/-- The same value computed from the coordinates `(3, 4)`, independently of the lemma. -/
example : ‖(EuclideanSpace.single 0 3 + EuclideanSpace.single 1 4 :
    EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 25 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Fin.sum_univ_two]
  norm_num

/-- Orthogonality is needed: for the parallel vectors `1, 1` in `ℝ`, the squared norm of the
sum is `4`, not `1 + 1`. -/
example : ‖∑ i : Fin 2, (![1, 1] : Fin 2 → ℝ) i‖ ^ 2 ≠
    ∑ i : Fin 2, ‖(![1, 1] : Fin 2 → ℝ) i‖ ^ 2 := by
  simp [Fin.sum_univ_two]
  norm_num

/-- A unit vector split along the coordinate axes: `‖(3/5, 4/5)‖ = 1` gives
`(3/5)^2 + (4/5)^2 = 1`. -/
example (v : Fin 2 → EuclideanSpace ℝ (Fin 2))
    (hv : v = ![EuclideanSpace.single 0 (3 / 5), EuclideanSpace.single 1 (4 / 5)]) :
    ∑ i, ‖v i‖ ^ 2 = 1 := by
  subst hv
  refine sum_norm_sq_eq_one_of_norm_sum_eq_one (𝕜 := ℝ) _ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [EuclideanSpace.inner_single_left]
  · rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp [Fin.sum_univ_two]
    norm_num

end
