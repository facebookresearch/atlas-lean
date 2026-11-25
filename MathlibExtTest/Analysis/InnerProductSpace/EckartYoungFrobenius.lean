/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.EckartYoungFrobenius

/-! Tests for Eckart–Young in the Frobenius norm: generic restatements of both
forms and a concrete diagonal example. -/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace MathlibExtTest.Analysis.InnerProductSpace.EckartYoungFrobenius

open Matrix.EckartYoungFrobenius

example {m n : ℕ} (A G : Matrix (Fin m) (Fin n) ℝ) {k : ℕ} (hG : G.rank ≤ k) :
    singularTailSq A k ≤ frobSq (A - G) :=
  singularTailSq_le_frobSq_sub A G hG

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    IsLeast {x : ℝ | ∃ G : Matrix (Fin m) (Fin n) ℝ, G.rank ≤ k ∧ x = frobSq (A - G)}
      (singularTailSq A k) :=
  isLeast_frobSq_sub A k

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    IsLeast {x : ℝ | ∃ G : Matrix (Fin m) (Fin n) ℝ, G.rank ≤ k ∧
        x = frobSq (P * (A - G) * Q)} (singularTailSq (P * A * Q) k) :=
  isLeast_frobSq_whitened A k P Q hP hQ

/-- Concrete value: for `A = diag(3, 1)`, `frobSq A = 10 = 3² + 1²`, the sum
of all squared singular values. -/
example : frobSq (!![3, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 10 := by
  norm_num [frobSq, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Rank-zero tail on a concrete matrix: `singularTailSq A 0 = frobSq A`. -/
example : singularTailSq (!![3, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) 0 = 10 := by
  have e : singularTailSq (!![3, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) 0 =
      frobSq (!![3, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [frobSq_eq_sum_sq_singularSeq, singularTailSq]
    exact Finsupp.sum_congr fun j _ => by rw [ite_eq_left (Nat.zero_le j)]
  rw [e]
  norm_num [frobSq, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Rank-one tail of a rank-one matrix is `0`: attained by the matrix itself,
and every tail is nonnegative. -/
example : singularTailSq (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 = 0 := by
  have hle := (isLeast_frobSq_sub (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1).2
  have hmem : frobSq (((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)) -
      (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)) ∈
      {x : ℝ | ∃ G : Matrix (Fin 2) (Fin 2) ℝ, G.rank ≤ 1 ∧
        x = frobSq ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) - G)} := by
    refine ⟨!![1, 0; 0, 0], ?_, rfl⟩
    rw [show (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
        Matrix.vecMulVec ![1, 0] ![1, 0] by
      ext i j
      fin_cases i <;> fin_cases j <;> simp]
    exact Matrix.rank_vecMulVec_le _ _
  have h0 : singularTailSq (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 ≤ 0 := by
    have h := hle hmem
    simpa [frobSq] using h
  have hnn : 0 ≤ singularTailSq (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 := by
    rw [singularTailSq]
    exact Finsupp.sum_nonneg fun j _ => by split_ifs <;> positivity
  linarith

/-- Whitening with identity changes of basis recovers the unweighted minimum. -/
example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    IsLeast {x : ℝ | ∃ G : Matrix (Fin m) (Fin n) ℝ, G.rank ≤ k ∧
        x = frobSq ((1 : Matrix (Fin m) (Fin m) ℝ) * (A - G) *
          (1 : Matrix (Fin n) (Fin n) ℝ))} (singularTailSq A k) := by
  have h := isLeast_frobSq_whitened A k 1 1 (by simp) (by simp)
  simpa using h

end MathlibExtTest.Analysis.InnerProductSpace.EckartYoungFrobenius
