/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.Basic
import MathlibExt.NumberTheory.FermatPolygonal

/-!
# Multiplicative functions additive on sums of two positive triangular numbers

Park's theorem classifies multiplicative complex-valued arithmetic functions `f` satisfying
`f (a + b) = f a + f b` whenever both `a` and `b` are sums of two positive triangular numbers.
It yields the identity or vanishing outside `{1, 3, 5}` with `f 3 * f 5 = 0`. The natural-number
formulation includes `0`, where arithmetic functions vanish by definition.
The small-value lemmas evaluate sums of admissible summands and products of coprime factors.

## References

* Poo-Sung Park, *Multiplicative Functions Additive on the Sums of Two Positive Triangular
  Numbers*, Journal of Integer Sequences 28 (2025), Article 25.4.8, pp. 1–6,
  Theorem 1 and Lemmas 2–5. <https://cs.uwaterloo.ca/journals/JIS/VOL28/Park/park10.html>
* Gauss's three-triangular-number theorem, stated in the introduction to Melvyn B. Nathanson,
  *A Short Proof of Cauchy's Polygonal Number Theorem*, Proceedings of the American Mathematical
  Society 99 (1987), pp. 22–24. We use `Nat.exists_eq_add_add_triangular` from
  `MathlibExt.NumberTheory.FermatPolygonal`.
* The auxiliary bound `small_triangular_sums` comes from the original tests in
  `MathlibExtTest.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditive`.
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

/-- **Park's Lemma 2: the identity up to 21 when the value at 2 is nonzero.** Let $f$ be a
multiplicative arithmetic function with values in $\mathbb{C}$ such that $f(a + b) = f(a) + f(b)$
whenever $a$ and $b$ are both sums of two positive triangular numbers. If $f(2) \neq 0$, then
$f(n) = n$ for every natural number $n \le 21$.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Lemma 2. -/
theorem multiplicative_additive_on_sum_two_triangular_eq_id_le_21
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b)
    (hf2 : f 2 ≠ 0) :
    ∀ n : ℕ, n ≤ 21 → f n = (n : ℂ) := by
  have t2 : IsSumTwoPositiveTriangular 2 := ⟨1, 1, by decide⟩
  have t4 : IsSumTwoPositiveTriangular 4 := ⟨1, 2, by decide⟩
  have t6 : IsSumTwoPositiveTriangular 6 := ⟨2, 2, by decide⟩
  have t7 : IsSumTwoPositiveTriangular 7 := ⟨1, 3, by decide⟩
  have t9 : IsSumTwoPositiveTriangular 9 := ⟨2, 3, by decide⟩
  have t12 : IsSumTwoPositiveTriangular 12 := ⟨3, 3, by decide⟩
  have t13 : IsSumTwoPositiveTriangular 13 := ⟨2, 4, by decide⟩
  -- Comparing the sum and product at 6 and 14 determines f 3 and f 7.
  have add4 : f 4 = f 2 + f 2 := hadd 2 2 t2 t2
  have add6 : f 6 = f 2 + f 4 := hadd 2 4 t2 t4
  have mul6 : f 6 = f 2 * f 3 := hf.map_mul_of_coprime (show Nat.Coprime 2 3 by decide)
  have h3 : f 3 = 3 := by
    apply mul_left_cancel₀ hf2
    rw [← mul6, add6, add4]
    ring
  have mul12 : f 12 = f 3 * f 4 := hf.map_mul_of_coprime (show Nat.Coprime 3 4 by decide)
  have add14 : f 14 = f 2 + f 12 := hadd 2 12 t2 t12
  have mul14 : f 14 = f 2 * f 7 := hf.map_mul_of_coprime (show Nat.Coprime 2 7 by decide)
  have h7 : f 7 = 7 := by
    apply mul_left_cancel₀ hf2
    rw [← mul14, add14, mul12, h3, add4]
    ring
  -- The alternative decomposition 14 = 7 + 7 allows cancellation of f 7.
  have h2 : f 2 = 2 := by
    have h7_ne : f 7 ≠ 0 := by rw [h7]; norm_num
    apply mul_right_cancel₀ h7_ne
    rw [← mul14, show f 14 = f 7 + f 7 from hadd 7 7 t7 t7, two_mul]
  have sum_id {a b : ℕ} (ha : IsSumTwoPositiveTriangular a) (hb : IsSumTwoPositiveTriangular b)
      (ea : f a = (a : ℂ)) (eb : f b = (b : ℂ)) : f (a + b) = ((a + b : ℕ) : ℂ) := by
    rw [hadd a b ha hb, ea, eb, Nat.cast_add]
  have mul_id {a b : ℕ} (hab : Nat.Coprime a b) (ea : f a = (a : ℂ)) (eb : f b = (b : ℂ)) :
      f (a * b) = ((a * b : ℕ) : ℂ) := by
    rw [hf.map_mul_of_coprime hab, ea, eb, Nat.cast_mul]
  have h4 : f 4 = 4 := sum_id t2 t2 h2 h2
  have h6 : f 6 = 6 := mul_id (by decide) h2 h3
  have h5 : f 5 = 5 := by
    have add10 : f 10 = f 4 + f 6 := hadd 4 6 t4 t6
    have mul10 : f 10 = f 2 * f 5 := hf.map_mul_of_coprime (show Nat.Coprime 2 5 by decide)
    apply mul_left_cancel₀ hf2
    rw [← mul10, add10, h4, h6, h2]
    norm_num
  have h9 : f 9 = 9 := sum_id t2 t7 h2 h7
  have h12 : f 12 = 12 := mul_id (by decide) h3 h4
  have h13 : f 13 = 13 := sum_id t4 t9 h4 h9
  intro n hn
  interval_cases n
  · simpa only [Nat.cast_zero] using f.map_zero
  · simpa only [Nat.cast_one] using hf.map_one
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact sum_id t4 t4 h4 h4
  · exact h9
  · exact mul_id (by decide) h2 h5
  · exact sum_id t4 t7 h4 h7
  · exact h12
  · exact h13
  · exact mul_id (by decide) h2 h7
  · exact mul_id (by decide) h3 h5
  · exact sum_id t7 t9 h7 h9
  · exact sum_id t4 t13 h4 h13
  · exact mul_id (by decide) h2 h9
  · exact sum_id t7 t12 h7 h12
  · exact mul_id (by decide) h4 h5
  · exact mul_id (by decide) h3 h7

private theorem small_triangular_sums {n : ℕ} (hn : IsSumTwoPositiveTriangular n) :
    n = 2 ∨ n = 4 ∨ 6 ≤ n := by
  obtain ⟨a, b, ha, hb, hab⟩ := hn
  have gap (k : ℕ) (hk : 1 ≤ k) :
      k * (k + 1) = 2 ∨ k * (k + 1) = 6 ∨ 12 ≤ k * (k + 1) := by
    have cases : k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
    rcases cases with rfl | rfl | h
    · decide
    · decide
    · exact Or.inr (Or.inr (Nat.mul_le_mul h (Nat.succ_le_succ h)))
  rcases gap a ha with ha | ha | ha <;> rcases gap b hb with hb | hb | hb <;> omega

private theorem exists_add_of_gt_twenty_one {n : ℕ} (hn : 21 < n) :
    ∃ a b, IsSumTwoPositiveTriangular a ∧ IsSumTwoPositiveTriangular b ∧ n = a + b := by
  let t := Nat.polygonalNumber 3
  have pair {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
      IsSumTwoPositiveTriangular (t i + t j) := by
    refine ⟨i, j, by omega, by omega, ?_⟩
    change 2 * (Nat.polygonalNumber 3 i + Nat.polygonalNumber 3 j) = _
    rw [Nat.mul_add, Nat.polygonalNumber_three, Nat.polygonalNumber_three,
      Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one i),
      Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one j)]
  have pack (i j k l : ℕ) (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0) (hl : l ≠ 0)
      (he : n = t i + t j + (t k + t l)) :
      ∃ a b, IsSumTwoPositiveTriangular a ∧ IsSumTwoPositiveTriangular b ∧ n = a + b :=
    ⟨_, _, pair hi hj, pair hk hl, he⟩
  -- Replace 21 and any zero summands with 21, 6 + 15, or 1 + 10 + 10.
  have padTwo {i : ℕ} (hi : i ≠ 0) (he : n = t i + 21) :
      ∃ a b, IsSumTwoPositiveTriangular a ∧ IsSumTwoPositiveTriangular b ∧ n = a + b := by
    have h21 : t 1 + (t 4 + t 4) = 21 := by decide
    exact pack i 1 4 4 hi (by decide) (by decide) (by decide) (by omega)
  have padOne {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) (he : n = t i + t j + 21) :
      ∃ a b, IsSumTwoPositiveTriangular a ∧ IsSumTwoPositiveTriangular b ∧ n = a + b := by
    have h21 : t 3 + t 5 = 21 := by decide
    exact pack i j 3 5 hi hj (by decide) (by decide) (by omega)
  obtain ⟨x, y, z, h⟩ := Nat.exists_eq_add_add_triangular (n - 21)
  have hs : n = t x + t y + t z + 21 := by
    change n - 21 = t x + t y + t z at h
    omega
  have ht0 : t 0 = 0 := Nat.polygonalNumber_zero 3
  rcases eq_or_ne x 0 with rfl | hx <;> rcases eq_or_ne y 0 with rfl | hy <;>
    rcases eq_or_ne z 0 with rfl | hz <;> (try simp only [ht0, zero_add, add_zero] at hs)
  · omega
  · exact padTwo hz hs
  · exact padTwo hy hs
  · exact padOne hy hz hs
  · exact padTwo hx hs
  · exact padOne hx hz hs
  · exact padOne hx hy hs
  · have h21 : t 6 = 21 := by decide
    exact pack x y z 6 hx hy hz (by decide) (by omega)

/-- **Park's theorem on multiplicative functions additive on sums of two triangular numbers.**
Let $f$ be a multiplicative arithmetic function with values in $\mathbb{C}$ (so $f$ is defined on
the natural numbers with $f(0) = 0$) such that $f(a + b) = f(a) + f(b)$ whenever $a$ and $b$ are
both sums of two positive triangular numbers. Then either $f(n) = n$ for every natural number
$n$, or $f(n) = 0$ for every natural number $n \notin \{1, 3, 5\}$ and $f(3) f(5) = 0$.

Source: Poo-Sung Park, "Multiplicative Functions Additive on the Sums
of Two Positive Triangular Numbers", Theorem 1 (TeX label `thm1`). -/
theorem multiplicative_additive_on_sum_two_triangular_classification
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, IsSumTwoPositiveTriangular a →
      IsSumTwoPositiveTriangular b → f (a + b) = f a + f b) :
    (∀ n : ℕ, f n = (n : ℂ)) ∨
      ((∀ n : ℕ, n ≠ 1 ∧ n ≠ 3 ∧ n ≠ 5 → f n = 0) ∧ f 3 * f 5 = 0) := by
  by_cases hf2 : f 2 = 0
  · obtain ⟨h35, hsmall⟩ := small_values_of_two_eq_zero f hf hadd hf2
    refine Or.inr ⟨?_, h35⟩
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      rintro ⟨hn1, hn3, hn5⟩
      by_cases hn : n ≤ 21
      · rcases eq_or_ne n 0 with rfl | hn0
        · exact f.map_zero
        · exact hsmall n (by omega) hn hn3 hn5
      · obtain ⟨a, b, ha, hb, rfl⟩ := exists_add_of_gt_twenty_one (by omega : 21 < n)
        have ha' := small_triangular_sums ha
        have hb' := small_triangular_sums hb
        rw [hadd a b ha hb, ih a (by omega) ⟨by omega, by omega, by omega⟩,
          ih b (by omega) ⟨by omega, by omega, by omega⟩, add_zero]
  · refine Or.inl ?_
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hn : n ≤ 21
      · exact multiplicative_additive_on_sum_two_triangular_eq_id_le_21 f hf hadd hf2 n hn
      · obtain ⟨a, b, ha, hb, rfl⟩ := exists_add_of_gt_twenty_one (by omega : 21 < n)
        have ha' := small_triangular_sums ha
        have hb' := small_triangular_sums hb
        rw [hadd a b ha hb, ih a (by omega), ih b (by omega), Nat.cast_add]

end MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeTriangularAdditiveWanted
