/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.StirlingMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Basic

/-!
# Tests for the Stirling-like matrix decompositions

Throughout, `α = (2, 3, 4, …)`, i.e. `α_l = l + 2`.

* `S_α(3)`, `U_α(3)`, `R_α(3)`, `R̃_α(3)`, `S(3)` and `V(3)`, computed from the
  definitions by `norm_num`.
* Theorem 3 (both products multiplied out), Theorem 4 (`det S_α(3) = 160`,
  also from the explicit matrix) and Lemma 7 (`R_α(3) R̃_α(3) = 1`
  multiplied out) for these matrices.
* Lemmas 1 and 2, Propositions 5, 8 and 9 and Corollary 10 at small indices,
  with both sides evaluated directly, including the case `i > j` of
  Proposition 9 and the off-diagonal case of Corollary 10.
* The two closed forms for `S_{3,3} = 53` and the helper lemmas on small
  inputs.
* `#print axioms` for every theorem of the module.
-/

@[expose] public section

namespace MathlibExtTest.Combinatorics.Enumerative.StirlingMatrix

open MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted MetaMathlibExt
open Finset

/-- The test sequence `α_l = l + 2`. -/
abbrev α : ℕ → ℚ := fun l => l + 2

/-! ### The matrices for `n = 3`, computed from the definitions -/

example : stirlingLikeMatrix α 3 = !![2, 3, 4; 2, 8, 15; 2, 18, 53] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [stirlingLikeMatrix, stirlingLikeEntry]

example : uMatrix α 3 = !![2, 3, 4; 0, 5, 11; 0, 0, 16] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [uMatrix, uEntry]

example : rMatrix α 3 = !![2, -2, 1; 0, 5, -5; 0, 0, 8] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rMatrix, rEntry, psi, sum_range_succ, Nat.factorial]

example : rTildeMatrix α 3 = !![1/2, 1/5, 1/16; 0, 1/5, 1/8; 0, 0, 1/8] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rTildeMatrix, rTildeEntry, omega, sum_range_succ,
      Nat.descFactorial]

example : stirlingMatrix2 3 = !![1, 0, 0; 1, 1, 0; 1, 3, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [stirlingMatrix2, Nat.stirlingSecond]

example : vandermondeMatrix 3 = !![1, 1, 1; 1, 2, 3; 1, 4, 9] := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [vandermondeMatrix]

/-! ### Theorems 3 and 4 and Lemma 7 against these matrices -/

/-- Both products of Theorem 3, multiplied out. -/
example : (!![1, 0, 0; 1, 1, 0; 1, 3, 1] * !![2, 3, 4; 0, 5, 11; 0, 0, 16] :
      Matrix (Fin 3) (Fin 3) ℚ) = !![2, 3, 4; 2, 8, 15; 2, 18, 53] ∧
    (!![1, 1, 1; 1, 2, 3; 1, 4, 9] * !![2, -2, 1; 0, 5, -5; 0, 0, 8] :
      Matrix (Fin 3) (Fin 3) ℚ) = !![2, 3, 4; 2, 8, 15; 2, 18, 53] := by
  constructor <;> norm_num [Matrix.mul_fin_three]

example : stirlingLikeMatrix α 3 = stirlingMatrix2 3 * uMatrix α 3 ∧
    stirlingLikeMatrix α 3 = vandermondeMatrix 3 * rMatrix α 3 :=
  stirlingLikeMatrix_decomp α 3

/-- Theorem 4: `det S_α(3) = Ω(α, 1) Ω(α, 2) Ω(α, 3) = 2 · 5 · 16`, and the
same value from the explicit matrix. -/
example : (stirlingLikeMatrix α 3).det = 160 := by
  rw [stirlingLikeMatrix_det]
  norm_num [omega, prod_range_succ, sum_range_succ, Nat.descFactorial]

example : (!![2, 3, 4; 2, 8, 15; 2, 18, 53] : Matrix (Fin 3) (Fin 3) ℚ).det =
    160 := by
  norm_num [Matrix.det_fin_three]

/-- Lemma 7: `R_α(3) R̃_α(3) = 1`, multiplied out, and the theorem. -/
example : (!![2, -2, 1; 0, 5, -5; 0, 0, 8] *
      !![1/2, 1/5, 1/16; 0, 1/5, 1/8; 0, 0, 1/8] :
      Matrix (Fin 3) (Fin 3) ℚ) = 1 := by
  rw [Matrix.one_fin_three]
  norm_num [Matrix.mul_fin_three]

example : rTildeMatrix α 3 = (rMatrix α 3)⁻¹ :=
  rTildeMatrix_eq_inv α 3 (by
    rw [show Icc 1 3 = {1, 2, 3} by decide]
    norm_num [omega, sum_range_succ, Nat.descFactorial])

/-! ### Lemmas 1 and 2 -/

/-- Lemma 1: `U_{2,3} = Λ(α, 2, 3) = 11` and `U_{3,3} = Λ(α, 3, 3) = 16`. -/
example : uEntry α 2 3 = 11 ∧ lambda α 2 3 = 11 ∧ uEntry α 3 3 = 16 ∧
    lambda α 3 3 = 16 := by
  norm_num [uEntry, lambda, sum_range_succ, Nat.choose]

example : uEntry α 3 2 = 0 := uEntry_eq_zero_of_lt α 3 2 (by norm_num)

/-- Lemma 2 for the third column of `R_α(3)`: `1 - 5 + 8 = 4 = α_2`. -/
example : ∑ i ∈ Icc 1 3, rEntry α i 3 = 4 := by
  rw [show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [rEntry, psi, sum_range_succ, Nat.factorial]

example : ∑ i ∈ Icc 1 3, rEntry α i 3 = α 2 := sum_rEntry_col α 3 (by norm_num)

/-! ### Propositions 5, 8 and 9 and Corollary 10 -/

/-- Proposition 5 at `i = j = 3`: both sides are `S_{3,3} = 53`. -/
example : ∑ k ∈ Icc 1 (min 3 3), (Nat.stirlingSecond 3 k : ℚ) * lambda α k 3 =
      53 ∧
    ∑ k ∈ Icc (1 : ℕ) 3, (k : ℚ) ^ (3 - 1) *
      ((-1 : ℚ) ^ (3 - k) / (3 - k).factorial) * psi α k = 53 := by
  rw [min_self, show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [lambda, psi, sum_range_succ, Nat.stirlingSecond, Nat.choose,
    Nat.factorial]

example := sum_stirlingSecond_lambda α 3 2 (by norm_num) (by norm_num)

/-- Proposition 8 at `i = 2`, `j = 3`: both sides are `3 Ω(α, 3) = 48`. -/
example : ∑ k₁ ∈ Icc 1 2, ∑ k₂ ∈ Icc k₁ 3, (Nat.stirlingSecond 2 k₁ : ℚ) *
      (Nat.descFactorial (3 - 1) (k₂ - 1) : ℚ) * lambda α k₁ k₂ = 48 ∧
    (3 : ℚ) ^ (2 - 1) * omega α 3 = 48 := by
  rw [show Icc 1 2 = {1, 2} by decide, sum_pair (by norm_num),
    show Icc 1 3 = {1, 2, 3} by decide, show Icc 2 3 = {2, 3} by decide]
  norm_num [lambda, omega, sum_range_succ, Nat.stirlingSecond, Nat.choose,
    Nat.factorial, Nat.descFactorial]

/-- Proposition 9 at `i = 2`, `j = 3` (value `Λ(α, 2, 3) = 11`) and at
`i = 3`, `j = 2` (value `0`). -/
example : ∑ k₁ ∈ Icc 1 2, ∑ k₂ ∈ Icc (1 : ℕ) 3,
      (signedStirlingFirst 2 k₁ : ℚ) * (k₂ : ℚ) ^ (k₁ - 1) *
        ((-1 : ℚ) ^ (3 - k₂) / (3 - k₂).factorial) * psi α k₂ = 11 := by
  rw [show Icc 1 2 = {1, 2} by decide, show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [signedStirlingFirst, psi, sum_range_succ, Nat.stirlingFirst,
    Nat.factorial]

example : ∑ k₁ ∈ Icc 1 3, ∑ k₂ ∈ Icc (1 : ℕ) 2,
      (signedStirlingFirst 3 k₁ : ℚ) * (k₂ : ℚ) ^ (k₁ - 1) *
        ((-1 : ℚ) ^ (2 - k₂) / (2 - k₂).factorial) * psi α k₂ = 0 := by
  rw [show Icc 1 3 = {1, 2, 3} by decide, show Icc 1 2 = {1, 2} by decide]
  norm_num [signedStirlingFirst, psi, sum_range_succ, Nat.stirlingFirst,
    Nat.factorial]

example := sum_signed_psi_eq α 3 2 (by norm_num) (by norm_num)

/-- Corollary 10 at `(i, j) = (2, 2)` and `(2, 3)`, computed directly. -/
example : ∑ k₁ ∈ Icc 1 2, ∑ k₂ ∈ Icc (1 : ℕ) 2,
      (-1 : ℚ) ^ (2 - k₂) * (signedStirlingFirst 2 k₁ : ℚ) *
        (k₂ : ℚ) ^ (k₁ - 1) / ((2 - k₂).factorial * (k₂ - 1).factorial) =
      1 := by
  rw [show Icc 1 2 = {1, 2} by decide]
  norm_num [signedStirlingFirst, Nat.stirlingFirst, Nat.factorial]

example : ∑ k₁ ∈ Icc 1 2, ∑ k₂ ∈ Icc (1 : ℕ) 3,
      (-1 : ℚ) ^ (3 - k₂) * (signedStirlingFirst 2 k₁ : ℚ) *
        (k₂ : ℚ) ^ (k₁ - 1) / ((3 - k₂).factorial * (k₂ - 1).factorial) =
      0 := by
  rw [show Icc 1 2 = {1, 2} by decide, show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [signedStirlingFirst, Nat.stirlingFirst, Nat.factorial]

example := sum_signed_eq_delta 4 4 (by norm_num) (by norm_num)

/-! ### The closed forms and helper lemmas -/

/-- `S_{3,3} = 53` from the closed form behind `S_α = V R_α`. -/
example : stirlingLikeEntry α 3 3 = 53 := by
  rw [stirlingLikeEntry_succ, show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [psi, sum_range_succ, Nat.factorial]

/-- `S_{3,3} = 53` from the closed form behind `S_α = S U_α`. -/
example : stirlingLikeEntry α 3 3 = 53 := by
  rw [stirlingLikeEntry_eq_sum_stirlingSecond_mul_uEntry α
    (by norm_num : 3 < 4)]
  norm_num [sum_range_succ, uEntry, Nat.stirlingSecond]

example : uEntry α 3 3 = 16 := by
  rw [uEntry_self α 2]
  norm_num [omega, sum_range_succ, Nat.descFactorial]

example : uEntry α 2 4 = 19 := by
  rw [uEntry_add α 1 2]
  norm_num [sum_range_succ, Nat.factorial]

example (i : ℕ) : uEntry α i 0 = 0 ∧ uEntry α 0 i = 0 :=
  ⟨uEntry_zero_right α i, uEntry_zero_left α i⟩

/-- `Ω(α, 3) = 2! Ψ_α(3) = 2 · 8`. -/
example : omega α 3 = 16 := by
  rw [omega_succ α 2]
  norm_num [psi, sum_range_succ, Nat.factorial]

/-- Row `k` of `R_α(3)` against the column `(2↓₀, 2↓₁, 2↓₂) = (1, 2, 2)`:
`0` for `k = 2` and `Ω(α, 3) = 16` for `k = 3`. -/
example : ∑ m ∈ Icc 1 3, rEntry α 2 m * ((3 - 1).descFactorial (m - 1) : ℚ) =
      0 ∧
    ∑ m ∈ Icc 1 3, rEntry α 3 m * ((3 - 1).descFactorial (m - 1) : ℚ) =
      16 := by
  rw [show Icc 1 3 = {1, 2, 3} by decide]
  norm_num [rEntry, psi, sum_range_succ, Nat.factorial, Nat.descFactorial]

example : ∑ m ∈ Icc 1 3, rEntry α 2 m * ((3 - 1).descFactorial (m - 1) : ℚ) =
    0 := by
  rw [sum_rEntry_mul_descFactorial, ite_eq_right (by norm_num)]

/-- `(1 + 2)³ / 3! = ∑_{t ≤ 3} 2^{3-t} / (t! (3-t)!)`. -/
example : ((1 : ℚ) + 2) ^ 3 / Nat.factorial 3 = 9 / 2 := by
  rw [add_pow_div_factorial]
  norm_num [sum_range_succ, Nat.factorial]

example : ∑ t ∈ range 4, (-1 : ℚ) ^ t /
    (Nat.factorial t * Nat.factorial (3 - t)) = 0 := by
  norm_num [sum_range_succ, Nat.factorial]

example : ∑ t ∈ range 4, (-1 : ℚ) ^ t /
    (Nat.factorial t * Nat.factorial (3 - t)) = 0 :=
  sum_range_neg_one_pow_div_factorial_mul 3

example : ∑ t ∈ range 1, (-1 : ℚ) ^ (0 - t) /
    (Nat.factorial t * Nat.factorial (0 - t)) = 1 :=
  sum_range_neg_one_pow_sub_div_factorial_mul 0

/-- Pascal's rule summed against `2 ^ l` gives `3³ = 3 · 3²`. -/
example : ∑ l ∈ range 4, (Nat.choose 3 l : ℚ) * 2 ^ l = 27 := by
  rw [sum_range_choose_succ_mul (fun l => (2 : ℚ) ^ l) 2]
  norm_num [sum_range_succ, Nat.choose]

example (f : ℕ → ℚ) : ∑ k ∈ Icc 1 3, f k = f 1 + f 2 + f 3 := by
  rw [sum_Icc_one_eq_sum_range]
  norm_num [sum_range_succ]

example (f : ℕ → ℚ) : ∑ c : Fin 2, f (c.val + 1) = ∑ k ∈ Icc 1 2, f k :=
  sum_fin_eq_sum_Icc f 2

/-! ### Axioms -/

#print axioms add_pow_div_factorial
#print axioms sum_range_neg_one_pow_div_factorial_mul
#print axioms sum_range_neg_one_pow_sub_div_factorial_mul
#print axioms sum_Icc_one_eq_sum_range
#print axioms sum_range_choose_succ_mul
#print axioms sum_fin_eq_sum_Icc
#print axioms omega_succ
#print axioms sum_rEntry_col
#print axioms stirlingLikeEntry_succ
#print axioms uEntry_zero_right
#print axioms uEntry_zero_left
#print axioms uEntry_succ_succ
#print axioms uEntry_eq_zero_of_lt
#print axioms uEntry_add
#print axioms uEntry_eq_lambda
#print axioms stirlingLikeEntry_eq_sum_stirlingSecond_mul_uEntry
#print axioms stirlingLikeMatrix_decomp
#print axioms uEntry_self
#print axioms stirlingLikeMatrix_det
#print axioms sum_stirlingSecond_lambda
#print axioms sum_rEntry_mul_descFactorial
#print axioms rTildeMatrix_eq_inv
#print axioms sum_stirlingSecond_descFactorial_lambda
#print axioms sum_signed_psi_eq
#print axioms sum_signed_eq_delta

end MathlibExtTest.Combinatorics.Enumerative.StirlingMatrix
