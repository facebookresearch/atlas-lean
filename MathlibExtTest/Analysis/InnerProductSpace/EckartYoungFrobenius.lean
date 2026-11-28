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

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hgap : ∀ i < k, (Matrix.toEuclideanLin A).singularValues k <
      (Matrix.toEuclideanLin A).singularValues i)
    {B : Matrix (Fin m) (Fin n) ℝ} (hB : B.rank ≤ k)
    (hle : ‖A - B‖ ^ 2 ≤
      ∑ i ∈ Finset.Ico k n, (Matrix.toEuclideanLin A).singularValues i ^ 2) :
    B = truncSVD A k :=
  eq_truncSVD_of_frobenius_sub_sq_le A hgap hB hle

/-- Under the singular value gap the best rank-`k` approximation is unique. -/
example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hgap : ∀ i < k, (Matrix.toEuclideanLin A).singularValues k <
      (Matrix.toEuclideanLin A).singularValues i) :
    ∃! B : Matrix (Fin m) (Fin n) ℝ, B.rank ≤ k ∧
      ∀ G : Matrix (Fin m) (Fin n) ℝ, G.rank ≤ k → ‖A - B‖ ≤ ‖A - G‖ := by
  refine ⟨truncSVD A k, ⟨rank_truncSVD_le A k, fun G hG => ?_⟩, ?_⟩
  · have h := (isLeast_frobenius_sub_sq A k).2 ⟨G, hG, rfl⟩
    rw [← frobenius_sub_truncSVD_sq] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  · rintro B ⟨hB, hmin⟩
    refine eq_truncSVD_of_frobenius_sub_sq_le A hgap hB ?_
    rw [← frobenius_sub_truncSVD_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmin _ (rank_truncSVD_le A k)) 2

/-- With `k = 0` the gap condition is void, and the only matrix of rank `0` within the tail
distance is `truncSVD A 0`. -/
example {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (hB : B.rank ≤ 0)
    (hle : ‖A - B‖ ^ 2 ≤
      ∑ i ∈ Finset.Ico 0 n, (Matrix.toEuclideanLin A).singularValues i ^ 2) :
    B = truncSVD A 0 :=
  eq_truncSVD_of_frobenius_sub_sq_le A (fun i hi => absurd hi (Nat.not_lt_zero i)) hB hle

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
