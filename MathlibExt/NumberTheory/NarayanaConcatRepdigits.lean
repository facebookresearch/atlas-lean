/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Concatenations of repdigits and the Guzmán Sánchez–Luca bound

Ray and Bhoi use this logarithmic inequality to bound the indices of Narayana numbers
that are concatenations of two repdigits.
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

/-- Lemma 3 (Guzmán Sánchez and Luca): for real `r ≥ 1` and `H` with `H > (4r²)^r` and
`H > L / (log L)^r`, we have `L < 2^r H (log H)^r`. The hypothesis `H > 0` is implied by
`H > (4r²)^r` and is dropped.

Source: Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two
Base b Repdigits*, INTEGERS 24 (2024), Article A20, Lemma 3 (`integers-2024-A20-lem-3`). -/
public theorem lt_two_rpow_mul_mul_log_rpow {r H L : ℝ} (hr : 1 ≤ r)
    (hH : (4 * r ^ 2) ^ r < H) (hL : L / Real.log L ^ r < H) :
    L < 2 ^ r * H * Real.log H ^ r := by
  have hr₀ : 0 < r := by linarith
  have hbase : 4 ≤ 4 * r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hfour : 4 < H :=
    hbase.trans_lt ((Real.self_le_rpow_of_one_le (by linarith) hr).trans_lt hH)
  have hH₀ : 0 < H := by linarith
  have hlogH : 1 < Real.log H :=
    (Real.lt_log_iff_exp_lt hH₀).2 (Real.exp_one_lt_three.trans (by linarith))
  rw [mul_comm ((2 : ℝ) ^ r) H, mul_assoc, ← Real.mul_rpow (by norm_num) (by linarith)]
  by_cases hsmall : L ≤ 1
  · calc
      L ≤ 1 := hsmall
      _ < H := by linarith
      _ ≤ H * (2 * Real.log H) ^ r :=
        le_mul_of_one_le_right hH₀.le (Real.one_le_rpow (by linarith) hr₀.le)
  have hL₀ : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos (lt_of_not_ge hsmall)
  have hscale := Real.lt_log_of_rpow_lt (by positivity) hH
  rw [show 4 * r ^ 2 = (2 * r) ^ 2 by ring, Real.log_pow] at hscale
  have hquot := Real.log_lt_log (div_pos hL₀ (Real.rpow_pos_of_pos hlogL r)) hL
  rw [Real.log_div hL₀.ne' (by positivity), Real.log_rpow hlogL] at hquot
  -- Apply 2 log t ≤ t at t = log L / (2r) to bound the iterated logarithm.
  have ht := Real.two_mul_le_exp (x := Real.log (Real.log L / (2 * r)))
  rw [Real.exp_log (by positivity), Real.log_div hlogL.ne' (by positivity),
    le_div_iff₀ (by positivity)] at ht
  have hlog : Real.log L < 2 * Real.log H := by
    linear_combination 4 / 3 * hquot + 2 / 3 * hscale + 1 / 3 * ht
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hlogL r)).1 hL).trans_le
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlogL.le hlog.le hr₀.le) hH₀.le)

end

end MetaMathlibExt
