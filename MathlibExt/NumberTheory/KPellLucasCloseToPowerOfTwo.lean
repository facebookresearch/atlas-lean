/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Log.GuzmanSanchezLuca
public import MathlibExt.Combinatorics.Enumerative.PellLucasNumber
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# `k`-Pell–Lucas numbers close to a power of 2: proved lemmas

Proved statements from Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas
Numbers Close to a Power of 2*, INTEGERS 25 (2025), Article A67. The paper's other statements
are in `WantedExt.NumberTheory.KPellLucasCloseToPowerOfTwoWanted`.

## Main results

* `abs_log_one_add_lt_and_abs_lt_exp_sub_one` (Lemma 6): if `0 < a < 1` and `0 < |x| < a`, then
  `|log (1 + x)| < (-log (1 - a) / a) |x|` and `|x| < (a / (1 - e^{-a})) |eˣ - 1|`.
* `lt_two_rpow_mul_mul_log_rpow_of_one_lt` (Lemma 7) applies the Guzmán Sánchez–Luca bound
  to `x > 1`.

## Proof of Lemma 6

Both constants exceed `1`, because `log (1 - a) < -a` and `1 - a < e^{-a}`. For `x > 0` the
bounds follow from `log (1 + x) < x` and `x < eˣ - 1`. For `x < 0` put `t = -x / a`, so that
`0 < t < 1`, `1 + x = t (1 - a) + (1 - t) · 1` and `x = t (-a) + (1 - t) · 0`. The strict
concavity of `log` on `(0, ∞)` gives `t log (1 - a) < log (1 + x)`, and the strict convexity of
`exp` gives `eˣ < t e^{-a} + (1 - t)`; these are the two bounds.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **$k$-generalized Pell–Lucas numbers.** For natural numbers $k$ and $n$, the $k$-generalized
Pell–Lucas number $Q^{(k)}_n$ is the natural number defined by $Q^{(k)}_0 = Q^{(k)}_1 = 2$ and

$$Q^{(k)}_{n+2} = 2 Q^{(k)}_{n+1} + \sum_{j} Q^{(k)}_{n-j},$$

where $j$ runs over the integers with $0 \le j \le n$ and $j \le k - 2$. For $k \ge 2$ and
$n \ge k - 2$ this reads $Q^{(k)}_{n+2} = 2 Q^{(k)}_{n+1} + Q^{(k)}_n + \cdots + Q^{(k)}_{n+2-k}$;
for smaller $n$ the terms of negative index (the $k - 2$ initial zeros of the sequence) are
dropped, and for $k \le 1$ the sum is empty.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Introduction. -/
def kPellLucas (k : ℕ) : ℕ → ℕ
  | 0 => 2
  | 1 => 2
  | n + 2 =>
    2 * kPellLucas k (n + 1) + ∑ j ∈ Finset.range (min (k - 1) (n + 1)), kPellLucas k (n - j)
decreasing_by all_goals omega

/-- **Initial value of the generalized Pell–Lucas numbers.** For every natural number $k$, the
$k$-generalized Pell–Lucas number $Q^{(k)}_0$ equals $2$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Introduction. -/
theorem kPellLucas_zero (k : ℕ) : kPellLucas k 0 = 2 := by
  rw [kPellLucas]

/-- **The $k$-Pell–Lucas number of index one.** For every natural number $k$, the $k$-Pell–Lucas
number $Q^{(k)}_1$ equals $2$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Introduction. -/
theorem kPellLucas_one (k : ℕ) : kPellLucas k 1 = 2 := by
  rw [kPellLucas]

/-- **Recurrence for the $k$-Pell–Lucas numbers.** Let $Q^{(k)}_n$ denote the $k$-generalized
Pell–Lucas numbers. For all natural numbers $k$ and $n$ with $k \le n + 2$,
$Q^{(k)}_{n+2} = 2 Q^{(k)}_{n+1} + \sum_{j=0}^{k-2} Q^{(k)}_{n-j}$, where the sum is empty when
$k < 2$. So once all $k - 1$ earlier terms have nonnegative index, the full recurrence holds.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Introduction. -/
theorem kPellLucas_add_two (k n : ℕ) (hn : k - 2 ≤ n) :
    kPellLucas k (n + 2) =
      2 * kPellLucas k (n + 1) + ∑ j ∈ Finset.range (k - 1), kPellLucas k (n - j) := by
  rw [kPellLucas, min_eq_left (by omega)]

/-- **The $2$-generalized Pell–Lucas numbers are the Pell–Lucas numbers.** For every natural number
$n$, the $2$-generalized Pell–Lucas number $Q^{(2)}_n$ equals the $n$th Pell–Lucas number $Q_n$;
this is the sequence $2, 2, 6, 14, 34, \ldots$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Introduction. -/
theorem kPellLucas_two : kPellLucas 2 = pellLucas := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [kPellLucas]; rfl
    | 1 => rw [kPellLucas]; rfl
    | n + 2 =>
      rw [kPellLucas, pellLucas_add_two, ih (n + 1) (by omega), ← ih n (by omega)]
      simp

/-- **Two values of the $3$-generalized Pell–Lucas numbers.** The $3$-generalized Pell–Lucas
numbers $Q^{(3)}_n$ satisfy $Q^{(3)}_3 = 16$ and $Q^{(3)}_6 = 260$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Theorem 1. -/
theorem kPellLucas_three_small : kPellLucas 3 3 = 16 ∧ kPellLucas 3 6 = 260 := by
  constructor <;> simp [kPellLucas, Finset.sum_range_succ]

/-- **Linear bounds for the logarithm and the exponential near zero (Lemma 6).** Let $a$ and $x$
be real numbers with $0 < a < 1$ and $0 < |x| < a$. Then
$|\log(1 + x)| < \frac{-\log(1 - a)}{a} |x|$ and $|x| < \frac{a}{1 - e^{-a}} |e^x - 1|$.

The case $x = 0$, where both strict inequalities read $0 < 0$, is excluded.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 6 (`integers-2025-A67-lem-6`). -/
theorem abs_log_one_add_lt_and_abs_lt_exp_sub_one (a x : ℝ) (ha₀ : 0 < a)
    (ha₁ : a < 1) (hx : |x| < a) (hx₀ : x ≠ 0) :
    |Real.log (1 + x)| < -Real.log (1 - a) / a * |x| ∧
      |x| < a / (1 - Real.exp (-a)) * |Real.exp x - 1| := by
  obtain ⟨hxa, hxa'⟩ := abs_lt.mp hx
  -- Both constants exceed `1`.
  have hlog : Real.log (1 - a) < -a := by
    have := Real.log_lt_sub_one_of_pos (x := 1 - a) (by linarith) (by linarith)
    linarith
  have hexp : 1 - a < Real.exp (-a) := by
    have := Real.add_one_lt_exp (neg_ne_zero.mpr ha₀.ne')
    linarith
  have hd : 0 < 1 - Real.exp (-a) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha₀))
  have hc : 1 < -Real.log (1 - a) / a := (one_lt_div ha₀).mpr (by linarith)
  have hk : 1 < a / (1 - Real.exp (-a)) := (one_lt_div hd).mpr (by linarith)
  rcases hx₀.lt_or_gt with hneg | hpos
  · -- For `x < 0`, interpolate with the weight `t = -x / a` between `-a` and `0`.
    obtain ⟨t, ht₀, ht₁, htx⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = t * -a :=
      ⟨-x / a, div_pos (neg_pos.mpr hneg) ha₀, (div_lt_one ha₀).mpr (by linarith),
        by field_simp⟩
    subst htx
    rw [abs_of_neg hneg]
    constructor
    · -- Strict concavity of `log` at `1 + x = t (1 - a) + (1 - t) · 1`.
      have h := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < 1 - a))
        (Set.mem_Ioi.mpr one_pos) (by linarith : (1 : ℝ) - a ≠ 1) ht₀ (sub_pos.mpr ht₁)
        (add_sub_cancel t 1)
      have e : t • (1 - a) + (1 - t) • (1 : ℝ) = 1 + t * -a := by
        simp only [smul_eq_mul]
        ring
      rw [e, smul_eq_mul, smul_eq_mul, Real.log_one, mul_zero, add_zero] at h
      rw [abs_of_neg (Real.log_neg (by linarith) (by linarith))]
      have : -Real.log (1 - a) / a * -(t * -a) = -(t * Real.log (1 - a)) := by
        field_simp
      linarith
    · -- Strict convexity of `exp` at `x = t (-a) + (1 - t) · 0`.
      have h := strictConvexOn_exp.2 (Set.mem_univ (-a)) (Set.mem_univ 0)
        (neg_ne_zero.mpr ha₀.ne') ht₀ (sub_pos.mpr ht₁) (add_sub_cancel t 1)
      simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
      rw [abs_of_neg (sub_neg.mpr (Real.exp_lt_one_iff.mpr hneg)), div_mul_eq_mul_div,
        lt_div_iff₀ hd]
      linarith [mul_lt_mul_of_pos_left h ha₀]
  · -- For `x > 0`, use `log (1 + x) < x` and `x < eˣ - 1`; both constants exceed `1`.
    rw [abs_of_pos hpos]
    constructor
    · rw [abs_of_pos (Real.log_pos (by linarith))]
      calc Real.log (1 + x) < 1 + x - 1 :=
            Real.log_lt_sub_one_of_pos (by linarith) (by linarith)
        _ = x := by ring
        _ < -Real.log (1 - a) / a * x := lt_mul_of_one_lt_left hpos hc
    · have h := Real.add_one_lt_exp hx₀
      rw [abs_of_pos (by linarith : 0 < Real.exp x - 1)]
      calc x < Real.exp x - 1 := by linarith
        _ < a / (1 - Real.exp (-a)) * (Real.exp x - 1) :=
            lt_mul_of_one_lt_left (by linarith) hk

set_option linter.unusedVariables false in
/-- **Lemma 7.** If `ℓ ≥ 1`, `T > (4ℓ²)^ℓ` and `T > x / (log x)^ℓ`, then
`x < 2^ℓ T (log T)^ℓ`; stated for `x > 1`, where `(log x)^ℓ` is a real power of a positive
number.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 7 (`integers-2025-A67-lem-7`). -/
public theorem lt_two_rpow_mul_mul_log_rpow_of_one_lt (ℓ T x : ℝ)
    (hℓ : 1 ≤ ℓ) (hx : 1 < x)
    (hT : (4 * ℓ ^ 2) ^ ℓ < T) (hTx : x / Real.log x ^ ℓ < T) :
    x < 2 ^ ℓ * T * Real.log T ^ ℓ :=
  lt_two_rpow_mul_mul_log_rpow hℓ hT hTx

end

end MetaMathlibExt
