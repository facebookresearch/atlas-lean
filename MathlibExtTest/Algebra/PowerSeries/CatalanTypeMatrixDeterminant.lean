/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.PowerSeries.CatalanTypeMatrixDeterminant

/-! # Tests for the lower-triangular Catalan-type determinant -/

open MetaMathlibExt PowerSeries

example (m N : ℕ) (lam x : ℝ) (A : Polynomial ℤ) :
    let P : ℕ → ℝ := fun n ↦
      coeff n ((1 + C (Polynomial.aeval x A) * X) * trinomialNegPowSeries lam 1 m x m)
    (Matrix.of fun i j : Fin (N + 1) ↦ if j ≤ i then P (i - j) else 0).det = P 0 ^ (N + 1) :=
  det_catalanTypeLowerTriangular (m := m) (N := N) (lam := lam) (x := x) (A := A)

-- N = 0 is a one-by-one matrix. Even at m = 0 the formula uses the defined coefficient,
-- without replacing the formal substitution by a real-power expansion.
example (lam x : ℝ) (A : Polynomial ℤ) :
    let P : ℕ → ℝ := fun n ↦
      coeff n ((1 + C (Polynomial.aeval x A) * X) * trinomialNegPowSeries lam 1 0 x 0)
    (Matrix.of fun i j : Fin 1 ↦ if j ≤ i then P (i - j) else 0).det = P 0 := by
  intro P
  rw [Matrix.det_fin_one]
  simp [Matrix.of_apply]

-- The series is (1 + 5t)(1 - 2t + 3t²). The nonzero subdiagonal distinguishes the two
-- orientations even though taking determinants does not.
example :
    let P : ℕ → ℝ := fun n ↦ coeff n
      ((1 + C (Polynomial.aeval (3 : ℝ) (Polynomial.C (5 : ℤ))) * X) *
        trinomialNegPowSeries (-1) 1 2 3 2)
    let M := Matrix.of fun i j : Fin 2 ↦ if j ≤ i then P (i - j) else 0
    M 0 1 = 0 ∧ M 1 0 = 3 ∧ M.det = 1 := by
  intro P M
  have hK := trinomialNegPowSeries_neg_one 2 3 (m := 2) (by decide)
  have h0 : P 0 = 1 := by
    simp [P, hK]
  have hA : Polynomial.aeval (3 : ℝ) (Polynomial.C (5 : ℤ)) = 5 := by
    rw [Polynomial.aeval_C]; norm_num
  have h1 : P 1 = 3 := by
    simp only [P, hA, hK]
    norm_num [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, coeff_one, coeff_X, pow_two]
  refine ⟨rfl, ?_, ?_⟩
  · change P 1 = 3
    exact h1
  · calc
      M.det = P 0 ^ 2 :=
        det_catalanTypeLowerTriangular 2 1 (-1) 3 (Polynomial.C 5)
      _ = 1 := by rw [h0, one_pow]

#print axioms det_catalanTypeLowerTriangular
