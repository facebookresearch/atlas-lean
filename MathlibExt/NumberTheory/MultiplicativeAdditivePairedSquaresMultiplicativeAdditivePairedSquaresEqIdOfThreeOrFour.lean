/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import MathlibExt.NumberTheory.MultiplicativeAdditiveEightSquares
import MathlibExt.NumberTheory.MultiplicativeAdditiveThreePairedSquares
import MathlibExt.NumberTheory.SixAndEightNonzeroSquares
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Multiplicative functions additive on six or eight paired squares

A complex-valued multiplicative function that is additive on three or four sums of two
positive squares, and nonzero at two, is the identity on positive integers. The four-pair
case is `multiplicative_additive_eight_squares_eq_id`; the three-pair case follows by strong
induction from the base values in `multiplicative_three_additive_two_squares_base`, using
that every integer `n ≥ 20` is a sum of six squares of positive integers
(`sum_six_and_eight_nonzero_squares`).

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 1 (`integers-2026-A121-thm-1`).
-/

namespace MetaMathlibExt

open ArithmeticFunction

namespace multiplicative_additive_paired_squares_eq_id_of_three_or_four

-- Every integer `n ≥ 20` is a sum of three weights `x j ^ 2 + y j ^ 2` with positive roots:
-- split the six positive squares of `sum_six_and_eight_nonzero_squares` into two halves.
private theorem six_squares {n : ℕ} (hn : 20 ≤ n) :
    ∃ x y : Fin 3 → ℕ, (∀ j, 0 < x j) ∧ (∀ j, 0 < y j) ∧
      ∑ j, (x j ^ 2 + y j ^ 2) = n := by
  obtain ⟨a, ha, hsum⟩ := sum_six_and_eight_nonzero_squares.1 n hn
  refine ⟨fun j ↦ a (Fin.castAdd 3 j), fun j ↦ a (Fin.natAdd 3 j),
    fun j ↦ Nat.pos_of_ne_zero (ha _), fun j ↦ Nat.pos_of_ne_zero (ha _), ?_⟩
  rw [Finset.sum_add_distrib]
  exact (Fin.sum_univ_add (fun i : Fin (3 + 3) ↦ a i ^ 2)).symm.trans hsum

-- A multiplicative function that is 3-additive on sums of two positive squares and nonzero
-- at two fixes every positive integer below 20.
private theorem small_values {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (add : ∀ A : Fin 3 → ℕ, (∀ i, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ A i = a ^ 2 + b ^ 2) →
      f (∑ i, A i) = ∑ i, f (A i))
    (h2 : f 2 ≠ 0) (n : ℕ) (hn : 0 < n) (hlt : n < 20) : f n = n := by
  obtain ⟨f2, f3, f5⟩ := multiplicative_three_additive_two_squares_base f hf add h2
  have e2 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2 = a ^ 2 + b ^ 2 :=
    ⟨1, 1, by decide, by decide, rfl⟩
  have e5 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 5 = a ^ 2 + b ^ 2 :=
    ⟨1, 2, by decide, by decide, rfl⟩
  have e8 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 8 = a ^ 2 + b ^ 2 :=
    ⟨2, 2, by decide, by decide, rfl⟩
  have e10 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 10 = a ^ 2 + b ^ 2 :=
    ⟨1, 3, by decide, by decide, rfl⟩
  have e18 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 18 = a ^ 2 + b ^ 2 :=
    ⟨3, 3, by decide, by decide, rfl⟩
  have e20 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 20 = a ^ 2 + b ^ 2 :=
    ⟨2, 4, by decide, by decide, rfl⟩
  have add_three {a b c : ℕ}
      (ha : ∃ a' b' : ℕ, 0 < a' ∧ 0 < b' ∧ a = a' ^ 2 + b' ^ 2)
      (hb : ∃ a' b' : ℕ, 0 < a' ∧ 0 < b' ∧ b = a' ^ 2 + b' ^ 2)
      (hc : ∃ a' b' : ℕ, 0 < a' ∧ 0 < b' ∧ c = a' ^ 2 + b' ^ 2) :
      f (a + b + c) = f a + f b + f c := by
    simpa only [Fin.sum_univ_three] using! add ![a, b, c] (by
      intro i
      fin_cases i <;> assumption)
  have prod (a b : ℕ) (hab : a.Coprime b) (ha : f a = a) (hb : f b = b) :
      f (a * b) = ↑(a * b) := by rw [hf.map_mul_of_coprime hab, ha, hb, Nat.cast_mul]
  have h10 : f 10 = 10 := by
    have h : f (2 * 5) = 10 := by
      rw [hf.map_mul_of_coprime rfl, f2, f5]
      norm_num
    simpa using h
  have h20mul : f 20 = f 4 * 5 := by
    have h : f (4 * 5) = f 4 * 5 := by rw [hf.map_mul_of_coprime rfl, f5]
    simpa using h
  -- The two triples for 24 together with `20 = 2 + 8 + 10` determine `f 4` and `f 8`.
  have eq20 := add_three e2 e8 e10
  have eq24a := add_three e8 e8 e8
  have eq24b := add_three e2 e2 e20
  change f 20 = _ at eq20
  change f 24 = _ at eq24a eq24b
  rw [f2, h10] at eq20
  rw [f2] at eq24b
  have v4 : f 4 = 4 := by linear_combination (3 * eq20 - eq24a + eq24b - 2 * h20mul) / 10
  have h20' : f 20 = 20 := by
    rw [v4] at h20mul
    linear_combination h20mul
  have v8 : f 8 = 8 := by linear_combination h20' - eq20
  have eq14 := add_three e2 e2 e10
  change f 14 = _ at eq14
  rw [f2, h10] at eq14
  have h14 : f 14 = 2 * f 7 := by
    have h : f (2 * 7) = 2 * f 7 := by rw [hf.map_mul_of_coprime rfl, f2]
    simpa using h
  have v7 : f 7 = 7 := by linear_combination (eq14 - h14) / 2
  have eq18 := add_three e2 e8 e8
  change f 18 = _ at eq18
  rw [f2, v8] at eq18
  have h18 : f 18 = 2 * f 9 := by
    have h : f (2 * 9) = 2 * f 9 := by rw [hf.map_mul_of_coprime rfl, f2]
    simpa using h
  have v9 : f 9 = 9 := by linear_combination (eq18 - h18) / 2
  have h18' : f 18 = 18 := by
    have h : f (2 * 9) = 18 := by
      rw [hf.map_mul_of_coprime rfl, f2, v9]
      norm_num
    simpa using h
  have eq22 := add_three e2 e10 e10
  change f 22 = _ at eq22
  rw [f2, h10] at eq22
  have h22 : f 22 = 2 * f 11 := by
    have h : f (2 * 11) = 2 * f 11 := by rw [hf.map_mul_of_coprime rfl, f2]
    simpa using h
  have v11 : f 11 = 11 := by linear_combination (eq22 - h22) / 2
  have eq26 := add_three e8 e8 e10
  change f 26 = _ at eq26
  rw [v8, h10] at eq26
  have h26 : f 26 = 2 * f 13 := by
    have h : f (2 * 13) = 2 * f 13 := by rw [hf.map_mul_of_coprime rfl, f2]
    simpa using h
  have v13 : f 13 = 13 := by linear_combination (eq26 - h26) / 2
  -- Since `32 = 2 * 16` is not a coprime factorization, use `48 = 3 * 16` instead.
  have eq48 := add_three e8 e20 e20
  change f 48 = _ at eq48
  rw [v8, h20'] at eq48
  have h48 : f 48 = 3 * f 16 := by
    have h : f (3 * 16) = 3 * f 16 := by rw [hf.map_mul_of_coprime rfl, f3]
    simpa using h
  have v16 : f 16 = 16 := by linear_combination (eq48 - h48) / 3
  have eq34 := add_three e8 e8 e18
  change f 34 = _ at eq34
  rw [v8, h18'] at eq34
  have h34 : f 34 = 2 * f 17 := by
    have h : f (2 * 17) = 2 * f 17 := by rw [hf.map_mul_of_coprime rfl, f2]
    simpa using h
  have v17 : f 17 = 17 := by linear_combination (eq34 - h34) / 2
  have eq38 := add_three e10 e10 e18
  change f 38 = _ at eq38
  rw [h10, h18'] at eq38
  have h38 : f 38 = 2 * f 19 := by
    have h : f (2 * 19) = 2 * f 19 := by rw [hf.map_mul_of_coprime rfl, f2]
    simpa using h
  have v19 : f 19 = 19 := by linear_combination (eq38 - h38) / 2
  interval_cases n <;> try assumption
  · simpa only [Nat.cast_one] using hf.1
  · exact prod 2 3 (by decide) f2 f3
  · exact prod 3 4 (by decide) f3 v4
  · exact prod 2 7 (by decide) f2 v7
  · exact prod 3 5 (by decide) f3 f5

-- A multiplicative function that is additive on three sums of two positive squares and
-- nonzero at two is the identity on positive integers.
private theorem three_case (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin 3 → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (h2 : f 2 ≠ 0) :
    ∀ n : ℕ, 0 < n → f n = n := by
  have add (A : Fin 3 → ℕ) (hA : ∀ i, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ A i = a ^ 2 + b ^ 2) :
      f (∑ i, A i) = ∑ i, f (A i) := by
    choose x y hx hy heq using hA
    simpa only [heq] using hadd x y hx hy
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    by_cases hlt : n < 20
    · exact small_values hf add h2 n hn hlt
    · obtain ⟨x, y, hx, hy, hsum⟩ := six_squares (Nat.le_of_not_gt hlt)
      have pos (j : Fin 3) : 0 < x j ^ 2 + y j ^ 2 :=
        Nat.add_pos_left (pow_pos (hx j) 2) _
      have lt (j : Fin 3) : x j ^ 2 + y j ^ 2 < n := by
        obtain ⟨k, hkj⟩ := exists_ne j
        rw [← hsum]
        exact Finset.single_lt_sum hkj (Finset.mem_univ _) (Finset.mem_univ _) (pos k)
          fun k _ _ ↦ (pos k).le
      calc
        f n = ∑ j, f (x j ^ 2 + y j ^ 2) := hsum ▸ hadd x y hx hy
        _ = ∑ j, ((x j ^ 2 + y j ^ 2 : ℕ) : ℂ) :=
          Finset.sum_congr rfl fun j _ ↦ ih _ (lt j) (pos j)
        _ = n := by rw [← Nat.cast_sum, hsum]

end multiplicative_additive_paired_squares_eq_id_of_three_or_four

open multiplicative_additive_paired_squares_eq_id_of_three_or_four in
/-- **Multiplicative functions additive on six or eight paired squares and nonzero at $2$ are
the identity.** Let $k \in \{3, 4\}$ and let $f$ be a complex-valued multiplicative function
with $f(2) \ne 0$ such that
$$f\Big(\sum_{j=1}^{k} (x_j^2 + y_j^2)\Big) = \sum_{j=1}^{k} f(x_j^2 + y_j^2)$$
for all positive integers $x_1, \dots, x_k, y_1, \dots, y_k$. Then $f(n) = n$ for every positive
integer $n$.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 1 (`integers-2026-A121-thm-1`). -/
public theorem multiplicative_additive_paired_squares_eq_id_of_three_or_four
    (k : ℕ) (hk : k = 3 ∨ k = 4) (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin k → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (h2 : f 2 ≠ 0) :
    ∀ n : ℕ, 0 < n → f n = n := by
  rcases hk with rfl | rfl
  · exact three_case f hf hadd h2
  · exact multiplicative_additive_eight_squares_eq_id f hf hadd h2

end MetaMathlibExt
