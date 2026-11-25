/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Tactic.IntervalCases

/-!
# Multiplicative functions additive on sums of two positive triangular numbers

Park's vanishing lemma follows by evaluating small integers as sums of admissible summands
and as products of coprime factors.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted

/-- **Sums of two positive triangular numbers.** A natural number $n$ is a sum of two positive
triangular numbers if there are natural numbers $a \ge 1$ and $b \ge 1$ with
$2n = a(a+1) + b(b+1)$, that is, $n = \frac{a(a+1)}{2} + \frac{b(b+1)}{2}$. -/
def IsSumTwoPositiveTriangular (n : ℕ) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 2 * n = a * (a + 1) + b * (b + 1)

/-- **Park's Lemma 3: vanishing from 4 to 21 when the value at 2 is zero and at 3 is not.** Let
$f$ be a multiplicative arithmetic function with values in $\mathbb{C}$ such that
$f(a + b) = f(a) + f(b)$ whenever $a$ and $b$ are both sums of two positive triangular numbers.
If $f(2) = 0$ and $f(3) \neq 0$, then $f(n) = 0$ for every natural number $n$ with
$4 \le n \le 21$.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 3. -/
theorem multiplicative_additive_on_sum_two_triangular_zero_of_three_ne_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 = 0) (hf3 : f 3 ≠ 0) :
    ∀ n : ℕ, 4 ≤ n → n ≤ 21 → f n = 0 := by
  have t2 : IsSumTwoPositiveTriangular 2 := ⟨1, 1, by decide⟩
  have t4 : IsSumTwoPositiveTriangular 4 := ⟨1, 2, by decide⟩
  have t6 : IsSumTwoPositiveTriangular 6 := ⟨2, 2, by decide⟩
  have t9 : IsSumTwoPositiveTriangular 9 := ⟨2, 3, by decide⟩
  have t12 : IsSumTwoPositiveTriangular 12 := ⟨3, 3, by decide⟩
  have t13 : IsSumTwoPositiveTriangular 13 := ⟨2, 4, by decide⟩
  have sum_zero {a b : ℕ} (ha : IsSumTwoPositiveTriangular a) (hb : IsSumTwoPositiveTriangular b)
      (za : f a = 0) (zb : f b = 0) : f (a + b) = 0 := by
    rw [hadd a b ha hb, za, zb, add_zero]
  have double_zero (k : ℕ) (hk : Nat.Coprime 2 k) : f (2 * k) = 0 := by
    rw [hf.map_mul_of_coprime hk, hf2, zero_mul]
  -- At 18, compare the coprime product 2 * 9 with the sum 9 + 9.
  have h9 : f 9 = 0 :=
    add_self_eq_zero.mp ((hadd 9 9 t9 t9).symm.trans (double_zero 9 (by decide)))
  have h4 : f 4 = 0 := sum_zero t2 t2 hf2 hf2
  have h6 : f 6 = 0 := double_zero 3 (by decide)
  have h12 : f 12 = 0 := sum_zero t6 t6 h6 h6
  have h13 : f 13 = 0 := sum_zero t4 t9 h4 h9
  have h15 : f 15 = 0 := sum_zero t6 t9 h6 h9
  have h21 : f 21 = 0 := sum_zero t9 t12 h9 h12
  -- Cancel f 3 from f 15 and f 21 to obtain the values at 5 and 7.
  have cancel_three (k : ℕ) (hk : Nat.Coprime 3 k) (h : f (3 * k) = 0) : f k = 0 := by
    rw [hf.map_mul_of_coprime hk] at h
    exact (mul_eq_zero.mp h).resolve_left hf3
  intro n hlo hhi
  interval_cases n
  · exact h4
  · exact cancel_three 5 (by decide) h15
  · exact h6
  · exact cancel_three 7 (by decide) h21
  · exact sum_zero t2 t6 hf2 h6
  · exact h9
  · exact double_zero 5 (by decide)
  · exact sum_zero t2 t9 hf2 h9
  · exact h12
  · exact h13
  · exact double_zero 7 (by decide)
  · exact h15
  · exact sum_zero t4 t12 h4 h12
  · exact sum_zero t4 t13 h4 h13
  · exact double_zero 9 (by decide)
  · exact sum_zero t6 t13 h6 h13
  · exact (hf.map_mul_of_coprime (show Nat.Coprime 4 5 by decide)).trans (by rw [h4, zero_mul])
  · exact h21

end MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted
