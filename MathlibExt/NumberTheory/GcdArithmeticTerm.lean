/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The gcd-term sequence

We bound the coefficients of the generating function by counting pairs on a natural-number
antidiagonal.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **The gcd-term sequence.** For natural numbers $a$, $b$ and $n$, $s_{a,b}(n)$ is the rational
number that is the coefficient of $z^n$ in the inverse of the formal power series
$(z^a - 1)(z^b - 1)$ over $\mathbb{Q}$. For $a, b \ge 1$ this series has constant coefficient $1$,
so $s_{a,b}$ is the coefficient sequence of $f_{a,b}(z) = 1 / ((z^a - 1)(z^b - 1))$. If $a = 0$
or $b = 0$ the series is $0$, whose inverse is taken to be $0$, so $s_{a,b}(n) = 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Section 2 (definition of `s_{a,b}`). -/
public noncomputable def gcdTermSeq (a b n : ℕ) : ℚ :=
  coeff n (((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1))⁻¹

/-- **Initial value of the gcd-term sequence.** For natural numbers $a, b \ge 1$, the gcd-term
sequence satisfies $s_{a,b}(0) = 1$.

Source: Prunescu and Shunia, *Arithmetic-Term Representations for the Greatest Common Divisor*,
INTEGERS 26 (2026), Article A96, Section 2. -/
public theorem gcdTermSeq_zero (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : gcdTermSeq a b 0 = 1 := by
  have ha' : a ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  simp [gcdTermSeq, ha', hb']

/-- **Generating function of the gcd-term sequence.** For natural numbers $a, b \ge 1$, in the
ring $\mathbb{Q}[[z]]$ of formal power series, the gcd-term sequence $s_{a,b}$ satisfies
$$
(z^a - 1)(z^b - 1) \sum_{n \ge 0} s_{a,b}(n) z^n = 1.
$$

Source: Prunescu and Shunia, *Arithmetic-Term Representations for the Greatest Common Divisor*,
INTEGERS 26 (2026), Article A96, Section 2. -/
public theorem mul_mk_gcdTermSeq (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1) * PowerSeries.mk (gcdTermSeq a b) = 1 := by
  have ha' : a ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  have hmk : PowerSeries.mk (gcdTermSeq a b) =
      (((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1))⁻¹ := by
    ext n
    simp [gcdTermSeq]
  rw [hmk]
  apply PowerSeries.mul_inv_cancel
  simp [ha', hb']

namespace gcdTermSeq_le_gcdTermSeq_one_one

private theorem coeff_inv_one_sub_X_pow (d : ℕ) (hd : d ≠ 0) (k : ℕ) :
    coeff k ((1 - X ^ d : ℚ⟦X⟧)⁻¹) = if d ∣ k then 1 else 0 := by
  have hinv : (1 - X ^ d : ℚ⟦X⟧)⁻¹ = expand d hd (mk 1) := by
    apply (inv_eq_iff_mul_eq_one (by simp [hd])).2
    simpa using congrArg (expand d hd) (mk_one_mul_one_sub_eq_one ℚ)
  simp [hinv, coeff_expand]

private theorem eq_card (a b n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gcdTermSeq a b n =
      ((Finset.antidiagonal n).filter fun p => a ∣ p.1 ∧ b ∣ p.2).card := by
  have hden : (X ^ a - 1 : ℚ⟦X⟧) * (X ^ b - 1) = (1 - X ^ b) * (1 - X ^ a) := by
    ring
  rw [gcdTermSeq, hden, PowerSeries.mul_inv_rev, coeff_mul, Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro p _
  rw [coeff_inv_one_sub_X_pow a (by omega), coeff_inv_one_sub_X_pow b (by omega)]
  by_cases h : a ∣ p.1 <;> simp [h]

end gcdTermSeq_le_gcdTermSeq_one_one

open gcdTermSeq_le_gcdTermSeq_one_one in
/-- **The gcd-term sequence is bounded by $n + 1$.** Let $a, b \ge 1$ be natural numbers, at least
one of them greater than $1$, and let $s_{a,b}$ be the gcd-term sequence. For every natural
number $n$, $s_{a,b}(n) \le s_{1,1}(n) = n + 1$, and $s_{a,b}(n) = s_{1,1}(n)$ only if $n = 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Lemma 5. -/
public theorem gcdTermSeq_le_gcdTermSeq_one_one (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 1 < a ∨ 1 < b) (n : ℕ) :
    gcdTermSeq a b n ≤ gcdTermSeq 1 1 n ∧ gcdTermSeq 1 1 n = n + 1 ∧
      (gcdTermSeq a b n = gcdTermSeq 1 1 n → n = 0) := by
  have h₁₁ : gcdTermSeq 1 1 n = ((Finset.antidiagonal n).card : ℚ) := by
    simp [eq_card 1 1 n le_rfl le_rfl]
  rw [h₁₁, eq_card a b n ha hb]
  refine ⟨by exact_mod_cast Finset.card_filter_le _ _, by simp, ?_⟩
  intro heq
  have hall := Finset.card_filter_eq_iff.mp (Nat.cast_injective heq)
  cases n with
  | zero => rfl
  | succ k =>
    have ha₁ := (hall (1, k) (by simp [Nat.add_comm])).1
    have hb₁ := (hall (k, 1) (by simp)).2
    simp only [Nat.dvd_one] at ha₁ hb₁
    omega

open gcdTermSeq_le_gcdTermSeq_one_one in
/-- **The gcd-term sequence is integral and recovers the gcd.** Let $a, b \ge 1$ be natural
numbers and let $s_{a,b}$ be the gcd-term sequence. Every value $s_{a,b}(n)$ is a natural number,
and $s_{a,b}(ab) = \gcd(a, b) + 1$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Lemma 4. -/
public theorem gcdTermSeq_natural_and_eq_gcd_add_one (a b : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    (∀ n, ∃ m : ℕ, gcdTermSeq a b n = m) ∧ gcdTermSeq a b (a * b) = Nat.gcd a b + 1 := by
  constructor
  · intro n
    exact ⟨_, eq_card a b n ha hb⟩
  rw [eq_card a b (a * b) ha hb]
  norm_cast
  -- Since b divides ab, it divides ab - i exactly when it divides i.
  calc
    _ = ((Finset.range (a * b + 1)).filter (Nat.lcm a b ∣ ·)).card := by
      rw [Finset.Nat.antidiagonal_eq_map, Finset.filter_map, Finset.card_map]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro i hi
      change (a ∣ i ∧ b ∣ a * b - i) ↔ Nat.lcm a b ∣ i
      rw [Nat.dvd_sub_iff_right (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) (dvd_mul_left b a),
        Nat.lcm_dvd_iff]
    _ = a * b / Nat.lcm a b + 1 := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.Ioc_insert_left (Nat.zero_le (a * b)),
        Finset.filter_insert, ite_eq_left (dvd_zero _), Finset.card_insert_of_notMem (by simp),
        Nat.Ioc_filter_dvd_card_eq_div]
    _ = Nat.gcd a b + 1 := by
      rw [← Nat.gcd_mul_lcm a b, Nat.mul_div_cancel _ (Nat.lcm_pos ha hb)]

end

end MetaMathlibExt
