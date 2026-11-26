/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import MathlibExt.NumberTheory.MultiplicativeAdditiveThreePairedSquares
import MathlibExt.NumberTheory.SixAndEightNonzeroSquares
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Multiplicative functions additive on three sums of two positive squares are the identity

We show that a complex-valued multiplicative function which is additive on three sums of
two positive squares and nonzero at `2` fixes every positive integer, following the strong
induction in Jewel Mahajan, *Multiplicative functions additive on partitions of 2k nonzero
squares* (https://arxiv.org/abs/2606.29507).
-/

namespace MetaMathlibExt

open ArithmeticFunction

namespace multiplicative_additive_six_squares_eq_id

private def IsPair (n : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a ^ 2 + b ^ 2

private theorem small_values {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (add : ∀ A : Fin 3 → ℕ, (∀ i, IsPair (A i)) → f (∑ i, A i) = ∑ i, f (A i))
    (h2 : f 2 ≠ 0) (n : ℕ) (hn : 0 < n) (hlt : n < 26) : f n = n := by
  obtain ⟨v2, v3, v5⟩ :=
    multiplicative_three_additive_two_squares_base f hf add h2
  have p2 : IsPair 2 := ⟨1, 1, by decide, by decide, rfl⟩
  have p5 : IsPair 5 := ⟨1, 2, by decide, by decide, rfl⟩
  have p8 : IsPair 8 := ⟨2, 2, by decide, by decide, rfl⟩
  have p10 : IsPair 10 := ⟨1, 3, by decide, by decide, rfl⟩
  have p20 : IsPair 20 := ⟨2, 4, by decide, by decide, rfl⟩
  have three {a b c : ℕ} (ha : IsPair a) (hb : IsPair b) (hc : IsPair c) :
      f (a + b + c) = f a + f b + f c := by
    simpa only [Fin.sum_univ_three] using! add ![a, b, c] (by
      intro i
      fin_cases i <;> assumption)
  have v1 : f 1 = ((1 : ℕ) : ℂ) := by simpa only [Nat.cast_one] using hf.1
  have h10 : f 10 = 10 := by
    have e := hf.map_mul_of_coprime (m := 2) (n := 5) (by decide)
    rw [v2, v5] at e
    norm_num at e
    exact e
  have h6 : f 6 = 6 := by
    have e := three p2 p2 p2
    rw [v2] at e
    norm_num at e
    exact e
  have h12 : f 12 = 12 := by
    have e := three p2 p5 p5
    rw [v2, v5] at e
    norm_num at e
    exact e
  have v4 : f 4 = 4 := by
    have e := hf.map_mul_of_coprime (m := 4) (n := 3) (by decide)
    rw [v3] at e
    norm_num at e
    rw [h12] at e
    linear_combination -e / 3
  have v8 : f 8 = 8 := by
    have e := three p2 p2 p8
    rw [v2] at e
    norm_num at e
    rw [h12] at e
    linear_combination -e
  have v9 : f 9 = 9 := by
    have e := three p2 p2 p5
    rw [v2, v5] at e
    norm_num at e
    exact e
  have h14 : f 14 = 14 := by
    have e := three p2 p2 p10
    rw [v2, h10] at e
    norm_num at e
    exact e
  have v7 : f 7 = 7 := by
    have e := hf.map_mul_of_coprime (m := 2) (n := 7) (by decide)
    rw [v2] at e
    norm_num at e
    rw [h14] at e
    linear_combination -e / 2
  have h20 : f 20 = 20 := by
    have e := three p5 p5 p10
    rw [v5, h10] at e
    norm_num at e
    exact e
  have h22 : f 22 = 22 := by
    have e := three p2 p10 p10
    rw [v2, h10] at e
    norm_num at e
    exact e
  have v11 : f 11 = 11 := by
    have e := hf.map_mul_of_coprime (m := 2) (n := 11) (by decide)
    rw [v2] at e
    norm_num at e
    rw [h22] at e
    linear_combination -e / 2
  have h26 : f 26 = 26 := by
    have e := three p8 p8 p10
    rw [v8, h10] at e
    norm_num at e
    exact e
  have v13 : f 13 = 13 := by
    have e := hf.map_mul_of_coprime (m := 2) (n := 13) (by decide)
    rw [v2] at e
    norm_num at e
    rw [h26] at e
    linear_combination -e / 2
  have h48 : f 48 = 48 := by
    have e := three p8 p20 p20
    rw [v8, h20] at e
    norm_num at e
    exact e
  have v16 : f 16 = 16 := by
    have e := hf.map_mul_of_coprime (m := 3) (n := 16) (by decide)
    rw [v3] at e
    norm_num at e
    rw [h48] at e
    linear_combination -e / 3
  have h38 : f 38 = 38 := by
    have e := three p8 p10 p20
    rw [v8, h10, h20] at e
    norm_num at e
    exact e
  have v19 : f 19 = 19 := by
    have e := hf.map_mul_of_coprime (m := 2) (n := 19) (by decide)
    rw [v2] at e
    norm_num at e
    rw [h38] at e
    linear_combination -e / 2
  have h15 : f 15 = 15 := by
    have e := three p5 p5 p5
    rw [v5] at e
    norm_num at e
    exact e
  have h17 : f 17 = 17 := by
    have e := three p2 p5 p10
    rw [v2, v5, h10] at e
    norm_num at e
    exact e
  have h18 : f 18 = 18 := by
    have e := three p2 p8 p8
    rw [v2, v8] at e
    norm_num at e
    exact e
  have h21 : f 21 = 21 := by
    have e := three p5 p8 p8
    rw [v5, v8] at e
    norm_num at e
    exact e
  have h23 : f 23 = 23 := by
    have e := three p5 p8 p10
    rw [v5, v8, h10] at e
    norm_num at e
    exact e
  have h24 : f 24 = 24 := by
    have e := three p8 p8 p8
    rw [v8] at e
    norm_num at e
    exact e
  have h25 : f 25 = 25 := by
    have e := three p5 p10 p10
    rw [v5, h10] at e
    norm_num at e
    exact e
  interval_cases n <;> assumption

end multiplicative_additive_six_squares_eq_id

open multiplicative_additive_six_squares_eq_id in
/-- **Multiplicative functions additive on six paired squares and nonzero at $2$ are the
identity.** Let $f$ be a complex-valued multiplicative function with $f(2) \ne 0$ such that
$$f\Big(\sum_{j=1}^{3} (x_j^2 + y_j^2)\Big) = \sum_{j=1}^{3} f(x_j^2 + y_j^2)$$
for all positive integers $x_1, x_2, x_3, y_1, y_2, y_3$. Then $f(n) = n$ for every positive
integer $n$.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Theorem 3 (`integers-2026-A121-thm-3`). -/
public theorem multiplicative_additive_six_squares_eq_id (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ x y : Fin 3 → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
      f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2))
    (h2 : f 2 ≠ 0) :
    ∀ n : ℕ, 0 < n → f n = n := by
  have add (A : Fin 3 → ℕ) (hA : ∀ i, IsPair (A i)) : f (∑ i, A i) = ∑ i, f (A i) := by
    choose x y hx hy heq using hA
    simpa only [heq] using hadd x y hx hy
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    by_cases hlt : n < 26
    · exact small_values hf add h2 n hn hlt
    obtain ⟨A, hApos, hAsum⟩ := sum_six_and_eight_nonzero_squares.1 n (by omega)
    have hpos : ∀ i, 0 < A i := fun i ↦ Nat.pos_of_ne_zero (hApos i)
    have hx : ∀ j, 0 < ![A 0, A 2, A 4] j := by
      intro j
      fin_cases j
      · exact hpos 0
      · exact hpos 2
      · exact hpos 4
    have hy : ∀ j, 0 < ![A 1, A 3, A 5] j := by
      intro j
      fin_cases j
      · exact hpos 1
      · exact hpos 3
      · exact hpos 5
    have hsum : ∑ j, (![A 0, A 2, A 4] j ^ 2 + ![A 1, A 3, A 5] j ^ 2) = n := by
      rw [← hAsum]
      simp [Fin.sum_univ_three, Fin.sum_univ_six]
      ring
    have hadd3 := hadd ![A 0, A 2, A 4] ![A 1, A 3, A 5] hx hy
    rw [hsum] at hadd3
    have lt : ∀ j, ![A 0, A 2, A 4] j ^ 2 + ![A 1, A 3, A 5] j ^ 2 < n := by
      have hA := hAsum
      simp only [Fin.sum_univ_six] at hA
      have sq1 : ∀ i, 1 ≤ A i ^ 2 := fun i ↦ pow_pos (hpos i) 2
      intro j
      fin_cases j
      · change A 0 ^ 2 + A 1 ^ 2 < n
        have e2 := sq1 2
        have e3 := sq1 3
        have e4 := sq1 4
        have e5 := sq1 5
        omega
      · change A 2 ^ 2 + A 3 ^ 2 < n
        have e0 := sq1 0
        have e1 := sq1 1
        have e4 := sq1 4
        have e5 := sq1 5
        omega
      · change A 4 ^ 2 + A 5 ^ 2 < n
        have e0 := sq1 0
        have e1 := sq1 1
        have e2 := sq1 2
        have e3 := sq1 3
        omega
    calc
      f n = ∑ j, f (![A 0, A 2, A 4] j ^ 2 + ![A 1, A 3, A 5] j ^ 2) := hadd3
      _ = ∑ j, (((![A 0, A 2, A 4] j ^ 2 + ![A 1, A 3, A 5] j ^ 2 : ℕ)) : ℂ) :=
        Finset.sum_congr rfl fun j _ ↦
          ih _ (lt j) (Nat.add_pos_left (pow_pos (hx j) 2) _)
      _ = n := by rw [← Nat.cast_sum, hsum]

end MetaMathlibExt
