/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
public import MathlibExt.Analysis.SpecialFunctions.Log.GuzmanSanchezLuca
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence

/-!
# Concatenations of two repdigits in a general base

For a Narayana number made up of two blocks of repeated digits, the block lengths
give upper and lower bounds on the logarithmic growth of the sequence.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Concatenations of two repdigits in a general base.** A natural number $n$ is a
concatenation of two repdigits in base $b$ if there are digits $a_1, a_2$ with
$1 \le a_1 \le b - 1$, $0 \le a_2 \le b - 1$ and $a_1 \ne a_2$, and block lengths $l, m \ge 1$,
such that $(b - 1) n = a_1 (b^l - 1) b^m + a_2 (b^m - 1)$. The digit conditions force
$b \ge 2$, and the equation says that the base-$b$ expansion of $n$ is $l$ copies of $a_1$
followed by $m$ copies of $a_2$.

Because of the condition $a_1 \ne a_2$, a repdigit such as $4 = (11)_3$ is not a concatenation
of two repdigits in base $3$. For $b = 10$ this is the notion of a concatenation of two decimal
repdigits.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Section 1 (Equation (1)). -/
public def IsConcatTwoRepdigitsBase (b n : ℕ) : Prop :=
  ∃ a₁ a₂ l m : ℕ, 1 ≤ a₁ ∧ a₁ < b ∧ a₂ < b ∧ 1 ≤ l ∧ 1 ≤ m ∧ a₁ ≠ a₂ ∧
    (b - 1) * n = a₁ * (b ^ l - 1) * b ^ m + a₂ * (b ^ m - 1)

/-- **Examples of two-repdigit concatenations in bases 2 and 5.** The number $4$ is a
concatenation of two repdigits in base $2$, since $4 = (100)_2$, and the number $406$ is a
concatenation of two repdigits in base $5$, since $406 = (3111)_5$.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Theorem 1. -/
public theorem isConcatTwoRepdigitsBase_examples :
    IsConcatTwoRepdigitsBase 2 4 ∧ IsConcatTwoRepdigitsBase 5 406 :=
  ⟨⟨1, 0, 1, 2, by norm_num⟩, ⟨3, 1, 1, 3, by norm_num⟩⟩

namespace narayanaCowsSequence_concat_log_bounds

private theorem digit_bounds {b a₁ a₂ l m N : ℕ} (hb : 2 ≤ b) (ha₁ : 1 ≤ a₁)
    (ha₁b : a₁ < b) (ha₂b : a₂ < b) (hl : 1 ≤ l)
    (heq : (b - 1) * N = a₁ * (b ^ l - 1) * b ^ m + a₂ * (b ^ m - 1)) :
    b ^ (l + m - 1) ≤ N ∧ N < b ^ (l + m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  have hb₀ : 0 < b := by omega
  have hlead : (b - 1) * b ^ k ≤ b ^ (k + 1) - 1 := by
    rw [Nat.sub_one_mul, pow_succ, mul_comm b]
    have := Nat.pow_pos (n := k) hb₀
    omega
  constructor
  · apply Nat.le_of_mul_le_mul_left _ (by omega : 0 < b - 1)
    rw [heq, show k + 1 + m - 1 = k + m by omega, pow_add, ← mul_assoc]
    refine le_trans ?_ (Nat.le_add_right ..)
    exact Nat.mul_le_mul_right _ (hlead.trans (Nat.le_mul_of_pos_left _ ha₁))
  · apply Nat.lt_of_mul_lt_mul_left (a := b - 1)
    rw [heq, pow_add b (k + 1) m]
    calc
      _ ≤ (b - 1) * (b ^ (k + 1) - 1) * b ^ m + (b - 1) * (b ^ m - 1) := by
        gcongr <;> omega
      _ = (b - 1) * ((b ^ (k + 1) - 1) * b ^ m + (b ^ m - 1)) := by ring
      _ < (b - 1) * (b ^ (k + 1) * b ^ m) := by
        apply (Nat.mul_lt_mul_left (by omega : 0 < b - 1)).2
        have hmul := Nat.le_mul_of_pos_left (b ^ m) (Nat.pow_pos (n := k + 1) hb₀)
        have := Nat.pow_pos (n := m) hb₀
        rw [Nat.sub_one_mul]
        omega

private theorem growth_bounds {α : ℝ} (hα : α ^ 3 = α ^ 2 + 1) (h₁ : 1 < α) (k : ℕ) :
    (narayanaCowsSequence (k + 4) : ℝ) * α < α ^ (k + 4) ∧
      α ^ (k + 4) < narayanaCowsSequence (k + 4) * Real.exp 1 := by
  have h₂ : α < 3 / 2 := by
    by_contra! h
    have := mul_le_mul_of_nonneg_right (show 1 / 2 ≤ α - 1 by linarith) (sq_nonneg α)
    nlinarith [sq_nonneg (α - 3 / 2)]
  have hs₁ : 1 < α ^ 2 := one_lt_pow₀ h₁ (by decide)
  have hs₂ : α ^ 2 < (3 / 2 : ℝ) ^ 2 := pow_lt_pow_left₀ h₂ (by linarith) (by decide)
  have h₄ : α ^ 4 = α ^ 2 + α + 1 := by linear_combination (α + 1) * hα
  have h₅ : α ^ 5 = 2 * α ^ 2 + α + 1 := by linear_combination (α ^ 2 + α + 1) * hα
  have h₆ : α ^ 6 = 3 * α ^ 2 + α + 2 := by
    linear_combination (α ^ 3 + α ^ 2 + α + 2) * hα
  induction k using narayanaCowsSequence.induct with
  | case1 =>
    change 2 * α < α ^ 4 ∧ α ^ 4 < 2 * Real.exp 1
    constructor <;> linarith [Real.exp_one_gt_d9]
  | case2 =>
    change 3 * α < α ^ 5 ∧ α ^ 5 < 3 * Real.exp 1
    constructor <;> linarith [Real.exp_one_gt_d9]
  | case3 =>
    change 4 * α < α ^ 6 ∧ α ^ 6 < 4 * Real.exp 1
    constructor <;> linarith [Real.exp_one_gt_d9]
  | case4 k ih₂ ih₀ =>
    -- Powers of the characteristic root satisfy the same recurrence as the sequence.
    have hpow : α ^ (k + 4 + 3) = α ^ (k + 4 + 2) + α ^ (k + 4) := by
      rw [pow_add α (k + 4) 3, pow_add α (k + 4) 2, hα]
      ring
    rw [narayanaCowsSequence, Nat.cast_add, hpow, add_mul, add_mul]
    exact ⟨add_lt_add ih₂.1 ih₀.1, add_lt_add ih₂.2 ih₀.2⟩

end narayanaCowsSequence_concat_log_bounds

-- The digit-length estimates also hold when the two digits coincide.
set_option linter.unusedVariables false in
/-- **Logarithmic bounds for Narayana numbers that concatenate two repdigits.** Let $(N_n)$ be
Narayana's cows sequence and let $\alpha$ be a real number with $\alpha^3 = \alpha^2 + 1$ (so
$\alpha \approx 1.46557$ is the unique real root of $x^3 - x^2 - 1$). Let $b \ge 2$, $n \ge 1$
and $l, m \ge 1$ be natural numbers, and let $a_1, a_2$ be digits with $1 \le a_1 \le b - 1$,
$0 \le a_2 \le b - 1$ and $a_1 \ne a_2$. If $(b - 1) N_n = a_1 (b^l - 1) b^m + a_2 (b^m - 1)$,
that is, the base-$b$ expansion of $N_n$ is $l$ copies of $a_1$ followed by $m$ copies of
$a_2$, then $(l + m - 1) \log b + \log \alpha < n \log \alpha < (l + m) \log b + 1$.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Lemma 1 (`integers-2024-A20-lem-1`). -/
public theorem narayanaCowsSequence_concat_log_bounds {α : ℝ} (hα : α ^ 3 = α ^ 2 + 1)
    {n b a₁ a₂ l m : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (ha₁ : 1 ≤ a₁) (ha₁b : a₁ < b)
    (ha₂b : a₂ < b) (hl : 1 ≤ l) (hm : 1 ≤ m) (hne : a₁ ≠ a₂)
    (heq : (b - 1) * narayanaCowsSequence n = a₁ * (b ^ l - 1) * b ^ m + a₂ * (b ^ m - 1)) :
    ((l + m - 1 : ℕ) : ℝ) * Real.log b + Real.log α < n * Real.log α ∧
      n * Real.log α < ((l + m : ℕ) : ℝ) * Real.log b + 1 := by
  obtain ⟨hlo, hhi⟩ := narayanaCowsSequence_concat_log_bounds.digit_bounds
    hb ha₁ ha₁b ha₂b hl heq
  have hn₄ : 4 ≤ n := by
    have hN : 2 ≤ narayanaCowsSequence n := calc
      2 ≤ b := hb
      _ = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ (l + m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := hlo
    by_contra! h
    obtain rfl | rfl | rfl : n = 1 ∨ n = 2 ∨ n = 3 := by omega
    all_goals exact absurd hN (by decide)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn₄
  have h₁ : 1 < α := by
    by_contra! h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (sq_nonneg α)]
  have hg := narayanaCowsSequence_concat_log_bounds.growth_bounds hα h₁ k
  have hb₀ : 0 < (b : ℝ) := by positivity
  have hα₀ : 0 < α := zero_lt_one.trans h₁
  have hlow : (b : ℝ) ^ (l + m - 1) * α < α ^ (k + 4) :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hlo) hα₀.le).trans_lt hg.1
  have hupp : α ^ (k + 4) < (b : ℝ) ^ (l + m) * Real.exp 1 :=
    hg.2.trans (mul_lt_mul_of_pos_right (by exact_mod_cast hhi) (Real.exp_pos 1))
  constructor
  · simpa [Real.log_mul (pow_pos hb₀ _).ne' hα₀.ne', Real.log_pow] using
      Real.log_lt_log (by positivity) hlow
  · simpa [Real.log_mul (pow_pos hb₀ _).ne' (Real.exp_pos 1).ne', Real.log_pow] using
      Real.log_lt_log (pow_pos hα₀ _) hupp

end

end MetaMathlibExt
