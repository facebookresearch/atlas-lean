/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.StirlingSecondKindMatrices
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Basic

/-!
# Tests for matrices whose entries are Stirling numbers of the second kind

* `S^[1](3)`, `S^[2](3)`, `s(3)`, `V(3)`, `Ṽ(3)`, `E(3)`, `Q^[1](3)` and
  `Q^[2](3)`, computed from the definitions by `norm_num`.
* Theorem 2 and Corollaries 2 and 3, Lemmas 1, 2 and 3 and Theorem 3
  (`m = 1`) for these matrices, multiplied out; `det S^[2](3) = 36` from the
  explicit matrix and from Theorem 2; the empty case `n = 0`.
* Theorems 4–8 and Corollary 4 at small indices, with both sides evaluated
  directly, including the off-diagonal cases of Theorems 4 and 6, the case
  `j > i` of Theorem 7 and the boundary case `j = 0` of Theorems 6, 7 and 8.
* The public helper lemmas on small inputs.
* `#print axioms` for every public theorem of the module.
-/

@[expose] public section

namespace MathlibExtTest.Combinatorics.Enumerative.StirlingSecondKindMatrices

open MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted MetaMathlibExt
open Finset

/-! ### The matrices for `n = 3`, computed from the definitions -/

example : stirlingSecondShiftMatrix 1 3 = !![1, 1, 0; 1, 3, 1; 1, 7, 6] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [stirlingSecondShiftMatrix, Nat.stirlingSecond]

example : stirlingSecondShiftMatrix 2 3 = !![1, 3, 1; 1, 7, 6; 1, 15, 25] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [stirlingSecondShiftMatrix, Nat.stirlingSecond]

example : stirlingFirstMatrix 3 = !![1, 0, 0; -1, 1, 0; 2, -3, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [stirlingFirstMatrix, signedStirlingFirst, Nat.stirlingFirst]

example : stirlingVMatrix 3 = !![1, 1, 0; 0, 2, 1; 0, 0, 3] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [stirlingVMatrix]

example : stirlingVTildeMatrix 3 =
    !![1, -1/2, 1/6; 0, 1/2, -1/6; 0, 0, 1/3] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [stirlingVTildeMatrix, Nat.factorial]

example : shiftedVandermondeMatrix 3 = !![1, 1, 1; 2, 3, 4; 4, 9, 16] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [shiftedVandermondeMatrix]

example : stirlingQMatrix 1 3 = !![0, 1, -1; 0, 0, 1; 0, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [stirlingQMatrix, Nat.factorial]

example : stirlingQMatrix 2 3 = !![0, 1, -1; 0, 0, 2; 0, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [stirlingQMatrix, Nat.factorial]

/-! ### The matrix identities for `n = 3`, multiplied out -/

/-- Theorem 2 and Corollary 2: `S(3) V(3) = S^[1](3)` and
`S^[1](3) V(3) = S^[2](3)`. -/
example : (!![1, 0, 0; 1, 1, 0; 1, 3, 1] * !![1, 1, 0; 0, 2, 1; 0, 0, 3] :
      Matrix (Fin 3) (Fin 3) ℚ) = !![1, 1, 0; 1, 3, 1; 1, 7, 6] ∧
    (!![1, 1, 0; 1, 3, 1; 1, 7, 6] * !![1, 1, 0; 0, 2, 1; 0, 0, 3] :
      Matrix (Fin 3) (Fin 3) ℚ) = !![1, 3, 1; 1, 7, 6; 1, 15, 25] := by
  constructor <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Theorem 2: `det S^[2](3) = 3!^2 = 36`, from the explicit matrix and from
the theorem. -/
example : (!![1, 3, 1; 1, 7, 6; 1, 15, 25] : Matrix (Fin 3) (Fin 3) ℚ).det =
    36 := by
  norm_num [Matrix.det_fin_three]

example : (stirlingSecondShiftMatrix 2 3).det = 36 := by
  rw [(stirlingSecondShiftMatrix_eq_mul_pow 2 3).2]
  norm_num [Nat.factorial]

/-- Lemma 1: `V(3) Ṽ(3) = I_3`. -/
example : (!![1, 1, 0; 0, 2, 1; 0, 0, 3] *
      !![1, -1/2, 1/6; 0, 1/2, -1/6; 0, 0, 1/3] :
      Matrix (Fin 3) (Fin 3) ℚ) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- Lemma 2: `Q^[2](3) = Q^[1](3) (V(3) - I_3)`. -/
example : (!![0, 1, -1; 0, 0, 1; 0, 0, 0] * !![0, 1, 0; 0, 1, 1; 0, 0, 2] :
      Matrix (Fin 3) (Fin 3) ℚ) = !![0, 1, -1; 0, 0, 2; 0, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Lemma 3: `S(3) (V(3) - I_3) = E(3) Q^[1](3)`; both sides equal
`!![0, 1, 0; 0, 2, 1; 0, 4, 5]`. -/
example : (!![1, 0, 0; 1, 1, 0; 1, 3, 1] * !![0, 1, 0; 0, 1, 1; 0, 0, 2] :
      Matrix (Fin 3) (Fin 3) ℚ) = !![0, 1, 0; 0, 2, 1; 0, 4, 5] ∧
    (!![1, 1, 1; 2, 3, 4; 4, 9, 16] * !![0, 1, -1; 0, 0, 1; 0, 0, 0] :
      Matrix (Fin 3) (Fin 3) ℚ) = !![0, 1, 0; 0, 2, 1; 0, 4, 5] := by
  constructor <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Theorem 3 for `m = 1`: `S^[1](3) (Ṽ(3) s(3)) = I_3`. -/
example : (!![1, 1, 0; 1, 3, 1; 1, 7, 6] *
      (!![1, -1/2, 1/6; 0, 1/2, -1/6; 0, 0, 1/3] *
        !![1, 0, 0; -1, 1, 0; 2, -3, 1]) :
      Matrix (Fin 3) (Fin 3) ℚ) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- Corollary 3 with `m₁ = m₂ = 1`: `S^[1](3) s(3) S^[1](3) = S^[2](3)`. -/
example : (!![1, 1, 0; 1, 3, 1; 1, 7, 6] * !![1, 0, 0; -1, 1, 0; 2, -3, 1] *
      !![1, 1, 0; 1, 3, 1; 1, 7, 6] : Matrix (Fin 3) (Fin 3) ℚ) =
    !![1, 3, 1; 1, 7, 6; 1, 15, 25] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- For `n = 0` all matrices are empty. -/
example : stirlingSecondShiftMatrix 2 0 =
    stirlingMatrix2 0 * stirlingVMatrix 0 ^ 2 :=
  Subsingleton.elim _ _

/-! ### The summation identities at small indices, both sides evaluated -/

/-- Theorem 4 with `i = j = 3`, `m = 2`: `2 - 18 + 25 = 3^2`. -/
example : ∑ l ∈ Icc 1 3,
    signedStirlingFirst 3 l * (Nat.stirlingSecond (l + 2) 3 : ℤ) = 9 := by
  decide

/-- Theorem 4 with `i = 3 > j = 2`, `m = 2`: `6 - 21 + 15 = 0`. -/
example : ∑ l ∈ Icc 1 3,
    signedStirlingFirst 3 l * (Nat.stirlingSecond (l + 2) 2 : ℤ) = 0 := by
  decide

/-- Theorem 5 with `i = 2`, `j = 3`, `N = 2`: both sides equal `4`. -/
example : ∑ l ∈ range 3, (-1 : ℚ) ^ (2 - l) * (Nat.choose 2 l : ℚ) *
    (Nat.stirlingSecond (2 + l) 3 : ℚ) = 4 := by
  norm_num [sum_range_succ, Nat.stirlingSecond, Nat.choose]

example : ∑ k ∈ Ico (1 : ℕ) 3, (-1 : ℚ) ^ (3 - k + 1) * (k : ℚ) ^ (2 - 1) *
    ((k + 1 : ℕ) : ℚ) ^ (2 - 1) /
      (((k - 1).factorial : ℚ) * ((3 - k - 1).factorial : ℚ)) = 4 := by
  rw [show Ico 1 3 = {1, 2} by decide]
  norm_num [Nat.factorial]

/-- Corollary 4 with `i = 3`, `j = 2`: `S(4, 2) - S(3, 2) = 7 - 3 = 4`, and
the right side is `2^2 = 4`. -/
example : (Nat.stirlingSecond 4 2 : ℚ) - Nat.stirlingSecond 3 2 = 4 := by
  norm_num [Nat.stirlingSecond]

example : ∑ k ∈ Ico (1 : ℕ) 2,
    (-1 : ℚ) ^ (2 - k + 1) * ((k + 1 : ℕ) : ℚ) ^ (3 - 1) /
      (((k - 1).factorial : ℚ) * ((2 - k - 1).factorial : ℚ)) = 4 := by
  rw [show Ico 1 2 = {1} by decide]
  norm_num [Nat.factorial]

/-- Theorem 6 with `n = 3`, `i = 2` and `j = 2` (the diagonal) and `j = 1`. -/
example : ∑ k₁ ∈ Icc 1 3, ∑ k₂ ∈ Icc k₁ 3,
    (-1 : ℚ) ^ (k₂ - k₁) * ((k₁ - 1).factorial : ℚ) / (k₂.factorial : ℚ) *
      (Nat.stirlingSecond (2 + 1) k₁ : ℚ) * (signedStirlingFirst k₂ 2 : ℚ) =
    1 := by
  simp only [sum_Icc_one_eq_sum_range, sum_range_succ, sum_range_zero]
  rw [show Icc (0 + 1) 3 = {1, 2, 3} by decide,
    show Icc (1 + 1) 3 = {2, 3} by decide, show Icc (2 + 1) 3 = {3} by decide]
  norm_num [Nat.factorial, Nat.stirlingSecond, signedStirlingFirst,
    Nat.stirlingFirst]

example : ∑ k₁ ∈ Icc 1 3, ∑ k₂ ∈ Icc k₁ 3,
    (-1 : ℚ) ^ (k₂ - k₁) * ((k₁ - 1).factorial : ℚ) / (k₂.factorial : ℚ) *
      (Nat.stirlingSecond (2 + 1) k₁ : ℚ) * (signedStirlingFirst k₂ 1 : ℚ) =
    0 := by
  simp only [sum_Icc_one_eq_sum_range, sum_range_succ, sum_range_zero]
  rw [show Icc (0 + 1) 3 = {1, 2, 3} by decide,
    show Icc (1 + 1) 3 = {2, 3} by decide, show Icc (2 + 1) 3 = {3} by decide]
  norm_num [Nat.factorial, Nat.stirlingSecond, signedStirlingFirst,
    Nat.stirlingFirst]

/-- Theorem 7 with `i = 2`: for `j = 2` the sum is `-1/2 + 3/2 = S(2, 2)`,
and for `j = 3 > i` it is `1/6 - 1/2 + 1/3 = 0`. -/
example : ∑ k ∈ Icc 1 (min (2 + 1) 2),
    (-1 : ℚ) ^ (2 - k) * ((k - 1).factorial : ℚ) / ((2 : ℕ).factorial : ℚ) *
      (Nat.stirlingSecond (2 + 1) k : ℚ) = Nat.stirlingSecond 2 2 := by
  rw [show Icc 1 (min (2 + 1) 2) = {1, 2} by decide]
  norm_num [Nat.factorial, Nat.stirlingSecond]

example : ∑ k ∈ Icc 1 (min (2 + 1) 3),
    (-1 : ℚ) ^ (3 - k) * ((k - 1).factorial : ℚ) / ((3 : ℕ).factorial : ℚ) *
      (Nat.stirlingSecond (2 + 1) k : ℚ) = 0 := by
  rw [show Icc 1 (min (2 + 1) 3) = {1, 2, 3} by decide]
  norm_num [Nat.factorial, Nat.stirlingSecond]

/-- Theorem 8 with `n = 3`, `i = j = 2`, `m₁ = m₂ = 1`: the double sum is
`S(4, 2) = 7`. -/
example : ∑ k₁ ∈ Icc 1 3, ∑ k₂ ∈ Icc 1 k₁,
    (Nat.stirlingSecond (2 + 1) k₁ : ℤ) * signedStirlingFirst k₁ k₂ *
      (Nat.stirlingSecond (k₂ + 1) 2 : ℤ) = 7 := by
  decide

example : Nat.stirlingSecond (2 + 1 + 1) 2 = 7 := by
  decide

/-! ### Boundary cases of the summation identities -/

/-- Theorems 6 and 8 with `j = 0`: both sides vanish since `i ≥ 1`. -/
example : ∑ k₁ ∈ Icc 1 2, ∑ k₂ ∈ Icc 1 k₁,
    (Nat.stirlingSecond (1 + 1) k₁ : ℤ) * signedStirlingFirst k₁ k₂ *
      (Nat.stirlingSecond (k₂ + 1) 0 : ℤ) = 0 := by
  decide

example : ∑ k₁ ∈ Icc 1 2, ∑ k₂ ∈ Icc k₁ 2,
    (-1 : ℚ) ^ (k₂ - k₁) * ((k₁ - 1).factorial : ℚ) / (k₂.factorial : ℚ) *
      (Nat.stirlingSecond (1 + 1) k₁ : ℚ) * (signedStirlingFirst k₂ 0 : ℚ) =
    0 :=
  (sum_sum_stirlingSecond_signedStirlingFirst_eq_ite le_rfl
    (by norm_num)).trans (by norm_num)

/-- Theorem 7 with `j = 0`: the sum is empty. -/
example : ∑ k ∈ Icc 1 (min (1 + 1) 0),
    (-1 : ℚ) ^ (0 - k) * ((k - 1).factorial : ℚ) / ((0 : ℕ).factorial : ℚ) *
      (Nat.stirlingSecond (1 + 1) k : ℚ) = 0 := by
  simp

/-! ### Helper lemmas -/

example : (stirlingVMatrix 3 ^ 2) 2 1 = 0 := by
  rw [stirlingVMatrix_pow_apply_of_le 2 (by decide)]
  decide

example : (stirlingVMatrix 3 ^ 2) 2 2 = 9 := by
  rw [stirlingVMatrix_pow_apply_of_le 2 le_rfl]
  norm_num

example : stirlingFirstMatrix 3 * stirlingSecondShiftMatrix 2 3 =
    stirlingVMatrix 3 ^ 2 :=
  stirlingFirstMatrix_mul_stirlingSecondShiftMatrix 2 3

example : (stirlingVMatrix 4).det = 24 := by
  rw [det_stirlingVMatrix]
  norm_num [Nat.factorial]

example (f : ℕ → ℚ) :
    ∑ k ∈ range 2, f k = ∑ b : Fin 3, if b.val < 2 then f b.val else 0 :=
  sum_range_eq_sum_fin_ite (by norm_num) f

example (f : ℕ → ℚ) :
    ∑ l ∈ Icc 2 3, f l = ∑ l ∈ Icc 1 3, if 2 ≤ l then f l else 0 :=
  sum_Icc_eq_sum_Icc_one_ite (by norm_num) f

/-! ### Axioms -/

#print axioms stirlingSecondShiftMatrix_zero
#print axioms stirlingSecondShiftMatrix_apply_zero_right
#print axioms stirlingFirstMatrix_apply_self
#print axioms stirlingVMatrix_apply_self
#print axioms stirlingVTildeMatrix_apply_self
#print axioms shiftedVandermondeMatrix_apply_zero_left
#print axioms stirlingQMatrix_apply_of_le
#print axioms sum_range_eq_sum_fin_ite
#print axioms sum_Icc_eq_sum_Icc_one_ite
#print axioms mul_stirlingVMatrix_apply
#print axioms stirlingVMatrix_mul_apply
#print axioms stirlingVMatrix_mul_stirlingVTildeMatrix
#print axioms stirlingVMatrix_inv
#print axioms det_stirlingVMatrix
#print axioms det_stirlingMatrix2
#print axioms stirlingFirstMatrix_mul_stirlingMatrix2
#print axioms stirlingMatrix2_mul_stirlingFirstMatrix
#print axioms stirlingVMatrix_pow_apply_of_le
#print axioms stirlingSecondShiftMatrix_eq_mul_pow
#print axioms stirlingSecondShiftMatrix_succ
#print axioms stirlingFirstMatrix_mul_stirlingSecondShiftMatrix
#print axioms stirlingSecondShiftMatrix_add
#print axioms stirlingSecondShiftMatrix_mul_stirlingVTildeMatrix_pow_mul
#print axioms stirlingSecondShiftMatrix_inv
#print axioms stirlingSecondShiftMatrix_one_mul_stirlingVTildeMatrix
#print axioms mul_stirlingVMatrix_sub_one_apply
#print axioms stirlingQMatrix_succ
#print axioms stirlingQMatrix_eq_one_mul_pow
#print axioms sum_choose_stirlingSecond_eq_sum_pow
#print axioms sum_choose_stirlingSecond_eq
#print axioms stirlingSecond_succ_sub_eq_sum
#print axioms stirlingMatrix2_mul_sub_one
#print axioms stirlingMatrix2_mul_sub_one_pow
#print axioms sum_signedStirlingFirst_mul_stirlingSecond_add
#print axioms sum_sum_stirlingSecond_signedStirlingFirst_eq_ite
#print axioms sum_stirlingSecond_succ_eq_ite
#print axioms sum_sum_stirlingSecond_signedStirlingFirst_stirlingSecond

end MathlibExtTest.Combinatorics.Enumerative.StirlingSecondKindMatrices
