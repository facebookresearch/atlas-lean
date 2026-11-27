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

Park's vanishing lemmas when the value at 2 is zero follow by evaluating small integers
as sums of admissible summands and as products of coprime factors.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted

/-- **Sums of two positive triangular numbers.** A natural number $n$ is a sum of two positive
triangular numbers if there are natural numbers $a \ge 1$ and $b \ge 1$ with
$2n = a(a+1) + b(b+1)$, that is, $n = \frac{a(a+1)}{2} + \frac{b(b+1)}{2}$. -/
def IsSumTwoPositiveTriangular (n : ℕ) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 2 * n = a * (a + 1) + b * (b + 1)

private theorem small_values_of_two_eq_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 = 0) :
    f 3 * f 5 = 0 ∧ ∀ n : ℕ, 2 ≤ n → n ≤ 21 → n ≠ 3 → n ≠ 5 → f n = 0 := by
  have t2 : IsSumTwoPositiveTriangular 2 := ⟨1, 1, by decide⟩
  have t4 : IsSumTwoPositiveTriangular 4 := ⟨1, 2, by decide⟩
  have t6 : IsSumTwoPositiveTriangular 6 := ⟨2, 2, by decide⟩
  have t7 : IsSumTwoPositiveTriangular 7 := ⟨1, 3, by decide⟩
  have t9 : IsSumTwoPositiveTriangular 9 := ⟨2, 3, by decide⟩
  have t12 : IsSumTwoPositiveTriangular 12 := ⟨3, 3, by decide⟩
  have t13 : IsSumTwoPositiveTriangular 13 := ⟨2, 4, by decide⟩
  have sum_zero {a b : ℕ} (ha : IsSumTwoPositiveTriangular a) (hb : IsSumTwoPositiveTriangular b)
      (za : f a = 0) (zb : f b = 0) : f (a + b) = 0 := by
    rw [hadd a b ha hb, za, zb, add_zero]
  have double_zero (k : ℕ) (hk : Nat.Coprime 2 k) : f (2 * k) = 0 := by
    rw [hf.map_mul_of_coprime hk, hf2, zero_mul]
  -- For an odd admissible k, compare k + k with the coprime product 2 * k.
  have odd_zero {k : ℕ} (tk : IsSumTwoPositiveTriangular k) (hk : Nat.Coprime 2 k) :
      f k = 0 := by
    apply add_self_eq_zero.mp
    rw [← hadd k k tk tk, ← two_mul, double_zero k hk]
  have h9 : f 9 = 0 := odd_zero t9 (by decide)
  have h4 : f 4 = 0 := sum_zero t2 t2 hf2 hf2
  have h6 : f 6 = 0 := double_zero 3 (by decide)
  have h12 : f 12 = 0 := sum_zero t6 t6 h6 h6
  have h13 : f 13 = 0 := sum_zero t4 t9 h4 h9
  have h15 : f 15 = 0 := sum_zero t6 t9 h6 h9
  have h21 : f 21 = 0 := sum_zero t9 t12 h9 h12
  refine ⟨(hf.map_mul_of_coprime (show Nat.Coprime 3 5 by decide)).symm.trans h15, ?_⟩
  intro n hlo hhi hn3 hn5
  interval_cases n
  · exact hf2
  · exact (hn3 rfl).elim
  · exact h4
  · exact (hn5 rfl).elim
  · exact h6
  · exact odd_zero t7 (by decide)
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

/-- **Park's Lemma 5: vanishing from 2 to 21 when the values at 2, 3 and 5 are zero.** Let $f$
be a multiplicative arithmetic function with values in $\mathbb{C}$ such that
$f(a + b) = f(a) + f(b)$ whenever $a$ and $b$ are both sums of two positive triangular numbers.
If $f(2) = f(3) = f(5) = 0$, then $f(n) = 0$ for every natural number $n$ with $2 \le n \le 21$.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 5. -/
theorem multiplicative_additive_on_sum_two_triangular_zero_of_all_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 = 0) (hf3 : f 3 = 0) (hf5 : f 5 = 0) :
    ∀ n : ℕ, 2 ≤ n → n ≤ 21 → f n = 0 := by
  intro n hlo hhi
  rcases eq_or_ne n 3 with rfl | hn3
  · exact hf3
  rcases eq_or_ne n 5 with rfl | hn5
  · exact hf5
  exact (small_values_of_two_eq_zero f hf hadd hf2).2 n hlo hhi hn3 hn5

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
  obtain ⟨h35, vanish⟩ := small_values_of_two_eq_zero f hf hadd hf2
  intro n hlo hhi
  by_cases hn5 : n = 5
  · subst n
    exact (mul_eq_zero.mp h35).resolve_left hf3
  · exact vanish n (by omega) hhi (by omega) hn5

/-- **Park's Lemma 4: vanishing from 2 to 21 except at 5.** Let $f$ be a multiplicative
arithmetic function with values in $\mathbb{C}$ such that $f(a + b) = f(a) + f(b)$ whenever
$a$ and $b$ are both sums of two positive triangular numbers. If $f(2) = 0$ and $f(5) \neq 0$,
then $f(n) = 0$ for every natural number $n$ with $2 \le n \le 21$ and $n \neq 5$.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 4. -/
theorem multiplicative_additive_on_sum_two_triangular_zero_of_five_ne_zero
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 = 0) (hf5 : f 5 ≠ 0) :
    ∀ n : ℕ, 2 ≤ n → n ≤ 21 → n ≠ 5 → f n = 0 := by
  obtain ⟨h35, vanish⟩ := small_values_of_two_eq_zero f hf hadd hf2
  intro n hlo hhi hn5
  by_cases hn3 : n = 3
  · subst n
    exact (mul_eq_zero.mp h35).resolve_right hf5
  · exact vanish n hlo hhi hn3 hn5

end MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted
