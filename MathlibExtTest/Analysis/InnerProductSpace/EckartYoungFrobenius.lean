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
example : frobSq (![![3, 0], ![0, 1]] : Matrix (Fin 2) (Fin 2) ℝ) = 10 := by
  norm_num [frobSq, Fin.sum_univ_two]

end MathlibExtTest.Analysis.InnerProductSpace.EckartYoungFrobenius
