/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Log.GuzmanSanchezLuca
public import MathlibExt.Combinatorics.Enumerative.PellLucasNumber
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Tactic.LinearCombination

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
* `kPellLucas_close_two_pow_exponent_bounds` bounds the exponent of a nearby power of two.
* `lt_abs_sub_div_of_max_partialQuotient` (Lemma 5 (ii)) gives a lower bound for
  `|τ - y / x|` in terms of the largest partial quotient of `τ` up to the first convergent
  denominator exceeding `M`, for `0 < x < M`.

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

-- For r = 2.62, the inequality 2 + 1 / (r - 1) ≤ r makes 2 rⁿ dominate the recurrence
-- even when the truncated sum is extended to all earlier terms.
private theorem kPellLucas_close_two_pow_exponent_bounds.growth_bounds (k n : ℕ) :
    2 ^ n ≤ kPellLucas k n ∧ (kPellLucas k n : ℝ) ≤ 2 * 2.62 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => norm_num [kPellLucas_zero]
    | 1 => norm_num [kPellLucas_one]
    | n + 2 =>
      obtain ⟨hlo, hhi⟩ := ih (n + 1) (by omega)
      have hsum : ∑ j ∈ Finset.range (min (k - 1) (n + 1)), kPellLucas k (n - j) ≤
          ∑ j ∈ Finset.range (n + 1), kPellLucas k j := calc
        _ ≤ ∑ j ∈ Finset.range (n + 1), kPellLucas k (n - j) :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right ..))
        _ = _ := Finset.sum_range_reflect (kPellLucas k) (n + 1)
      rw [kPellLucas]
      constructor
      · rw [pow_succ]
        omega
      · calc
          _ ≤ 2 * (kPellLucas k (n + 1) : ℝ) +
              ∑ j ∈ Finset.range (n + 1), (kPellLucas k j : ℝ) := by
            exact_mod_cast Nat.add_le_add_left hsum _
          _ ≤ 2 * (2 * 2.62 ^ (n + 1)) + ∑ j ∈ Finset.range (n + 1), 2 * 2.62 ^ j := by
            gcongr with j hj
            exact (ih j (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))).2
          _ ≤ _ := by
            rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (2.62 : ℝ) ≠ 1),
              pow_succ (2.62 : ℝ) (n + 1)]
            norm_num [div_eq_mul_inv]
            linarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2.62) (n + 1)]

set_option linter.unusedVariables false in
/-- **Exponent bounds for $k$-Pell–Lucas numbers close to a power of two (Lemma 8).** Let $k$, $n$
and $m$ be natural numbers with $k \ge 2$, $n \ge 1$, $m \ge 2$ and $n \ge k + 1$, and let
$Q^{(k)}_n$ be the $n$th $k$-Pell–Lucas number. If $|Q^{(k)}_n - 2^m| < 2^{m/2}$, then
$0.69n - 1.69 < m < 1.39n + 3.78$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 8 (`integers-2025-A67-lem-8`). -/
public theorem kPellLucas_close_two_pow_exponent_bounds (k n m : ℕ) (hk : 2 ≤ k)
    (hn : 1 ≤ n) (hm : 2 ≤ m) (hkn : k + 1 ≤ n)
    (hclose : |(kPellLucas k n : ℝ) - 2 ^ m| < (2 : ℝ) ^ ((m : ℝ) / 2)) :
    (0.69 : ℝ) * n - 1.69 < m ∧ (m : ℝ) < 1.39 * n + 3.78 := by
  obtain ⟨hlo, hhi⟩ := kPellLucas_close_two_pow_exponent_bounds.growth_bounds k n
  have hhalf : (2 : ℝ) ^ ((m : ℝ) / 2) ≤ 2 ^ m / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨hleft, hright⟩ := abs_lt.mp hclose
  constructor
  · have hpow : (2 : ℝ) ^ n < 2 ^ (m + 1) := by
      rw [pow_succ]
      linarith [show (2 : ℝ) ^ n ≤ kPellLucas k n by exact_mod_cast hlo,
        pow_pos (by norm_num : (0 : ℝ) < 2) m]
    have hnm := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow
    calc
      (0.69 : ℝ) * n - 1.69 < n := by linarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
      _ ≤ m := by exact_mod_cast Nat.le_of_lt_succ hnm
  · have hbase : (2.62 : ℝ) ≤ 2 ^ (1.39 : ℝ) := by
      apply le_of_pow_le_pow_left₀ (n := 100) (by decide) (by positivity)
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hpow : (2 : ℝ) ^ (m : ℝ) < 2 ^ (1.39 * n + 2 : ℝ) := calc
      (2 : ℝ) ^ (m : ℝ) < 4 * (2.62 : ℝ) ^ n := by rw [Real.rpow_natCast]; linarith
      _ ≤ 4 * ((2 : ℝ) ^ (1.39 : ℝ)) ^ n := by gcongr
      _ = _ := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num [mul_comm]
    have := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow
    linarith

namespace lt_abs_sub_div_of_max_partialQuotient

open GenContFract
open GenContFract (of)

private theorem dens_monotone (x : ℝ) : Monotone (of x).dens :=
  monotone_nat_of_le_succ fun _ ↦ of_den_mono

private theorem den_pos (x : ℝ) (n : ℕ) : 0 < (of x).dens n :=
  calc
    0 < (of x).dens 0 := by simp
    _ ≤ (of x).dens n := dens_monotone x (Nat.zero_le n)

/-- The cross product with an integer pair satisfies the integral continuant recurrence. -/
private theorem exists_int_cross {x : ℝ} (hinf : ∀ i, ¬(of x).TerminatedAt i) (p q : ℤ)
    (n : ℕ) : ∃ z : ℤ, (z : ℝ) = p * ((of x).contsAux n).b - q * ((of x).contsAux n).a := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨-q, by simp⟩
  | one => exact ⟨p - q * ⌊x⌋, by simp [of_h_eq_floor]⟩
  | more n ih₀ ih₁ =>
    obtain ⟨u, hu⟩ := ih₀
    obtain ⟨v, hv⟩ := ih₁
    obtain ⟨gp, hgp⟩ := Option.ne_none_iff_exists'.mp (hinf n)
    obtain ⟨h₁, b, hb⟩ := of_partNum_eq_one_and_exists_int_partDen_eq hgp
    refine ⟨b * v + u, ?_⟩
    rw [Int.cast_add, Int.cast_mul, hu, hv, contsAux_recurrence hgp rfl rfl, hb, h₁]
    dsimp
    ring

/-- The determinant with the next convergent shows that even an unreduced representation
of a convergent has denominator at least the continuant denominator. -/
private theorem den_le_of_convs_eq {x : ℝ} (hinf : ∀ i, ¬(of x).TerminatedAt i) {n : ℕ}
    {p q : ℤ} (hq : 0 < (q : ℝ)) (heq : (of x).convs n = (p : ℝ) / q) :
    (of x).dens n ≤ q := by
  let g := of x
  have hcross := (div_eq_div_iff (den_pos x n).ne' hq.ne').mp heq
  obtain ⟨z, hz⟩ := exists_int_cross hinf p q (n + 2)
  change (z : ℝ) = p * g.dens (n + 1) - q * g.nums (n + 1) at hz
  have hdet := (SimpContFract.of x).determinant (hinf n)
  change g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1) = _ at hdet
  have hscale : z * g.dens n = q * (-1 : ℝ) ^ (n + 1) := by
    linear_combination g.dens n * hz + q * hdet - g.dens (n + 1) * hcross
  have habs : |(z : ℝ)| * g.dens n = q := by
    simpa [abs_mul, abs_pow, abs_of_pos hq, abs_of_pos (den_pos x n), g]
      using congrArg abs hscale
  have hz₀ : z ≠ 0 := by
    rintro rfl
    exact hq.ne (by simpa using habs)
  have hz₁ : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz₀
  rw [← habs]
  simpa using mul_le_mul_of_nonneg_right hz₁ (den_pos x n).le

/-- The next complete quotient is strictly below its integer part plus one. The preceding
denominator contributes at most one more copy of the current denominator. -/
private theorem convergent_lower_bound {x A : ℝ} {n : ℕ} (hinf : ¬(of x).TerminatedAt n)
    (ha : ∀ b : ℝ, (of x).partDens.get? n = some b → b ≤ A) :
    1 / ((A + 2) * (of x).dens n ^ 2) < |x - (of x).convs n| := by
  obtain ⟨next, hnext⟩ := Option.ne_none_iff_exists'.mp
    (mt of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr hinf)
  obtain ⟨s, hs, hs₀, rfl⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hnext
  have hdigit := partDen_eq_s_b (get?_of_eq_some_of_succ_get?_intFractPair_stream hnext)
  have ht : s.fr⁻¹ < A + 1 :=
    (Int.lt_floor_add_one _).trans_le (add_le_add_left (ha _ hdigit) 1)
  let D := (of x).dens n
  let P := ((of x).contsAux n).b
  have hD : 0 < D := den_pos x n
  have hP : 0 ≤ P := zero_le_of_contsAux_b
  have hPD : P ≤ D := by
    cases n with
    | zero => simp [P, D]
    | succ k => exact of_den_mono
  have hfr : 0 < s.fr := (IntFractPair.nth_stream_fr_nonneg hs).lt_of_ne' hs₀
  have herr : x - (of x).convs n = (-1) ^ n / (D * (s.fr⁻¹ * D + P)) := by
    simpa only [hs₀, ite_false, D, P, den_eq_conts_b, nth_cont_eq_succ_nth_contAux] using
      sub_convs_eq hs
  rw [herr, abs_div, abs_neg_one_pow, abs_of_pos (by positivity)]
  apply one_div_lt_one_div_of_lt (by positivity)
  calc
    D * (s.fr⁻¹ * D + P) < D * ((A + 1) * D + D) :=
      mul_lt_mul_of_pos_left (add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_right ht hD) hPD) hD
    _ = (A + 2) * D ^ 2 := by ring

end lt_abs_sub_div_of_max_partialQuotient

set_option linter.unusedVariables false in
/-- **Continued-fraction lower bound for rational approximations.** Let $\tau$ be an irrational real
number with simple continued fraction expansion $[a_0; a_1, a_2, \ldots]$, so that
$a_0 = \lfloor \tau \rfloor$, and let $q_0, q_1, \ldots$ be the denominators of its convergents. Let
$M > 0$ be a real number, let $N$ be the least positive integer with $q_N > M$, and put
$a(M) = \max \{a_k : 0 \le k \le N\}$. Then

$$\left|\tau - \frac{y}{x}\right| > \frac{1}{(a(M) + 2)\, x^2}$$

for all integers $x$ and $y$ with $0 < x < M$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 5 (`integers-2025-A67-lem-5`). -/
public theorem lt_abs_sub_div_of_max_partialQuotient (τ : ℝ) (hτ : Irrational τ) (M : ℝ)
    (hM : 0 < M) (N : ℕ) (hN : 0 < N) (hqN : M < (GenContFract.of τ).dens N)
    (hNmin : ∀ j, 0 < j → j < N → (GenContFract.of τ).dens j ≤ M) (a : ℕ → ℝ)
    (ha₀ : a 0 = (GenContFract.of τ).h)
    (ha : ∀ j, (GenContFract.of τ).partDens.get? j = some (a (j + 1))) (x y : ℤ) (hx : 0 < x)
    (hxM : (x : ℝ) < M) :
    1 / (((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one a + 2) * (x : ℝ) ^ 2) <
      |τ - y / x| := by
  let A : ℝ := (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one a
  have hinf (i : ℕ) : ¬(GenContFract.of τ).TerminatedAt i := by
    intro hi
    obtain ⟨r, hr⟩ := GenContFract.exists_rat_eq_of_terminates ⟨i, hi⟩
    exact hτ ⟨r, hr.symm⟩
  have hx' : 0 < (x : ℝ) := by exact_mod_cast hx
  have hA1 : 1 ≤ A := by
    have hmem : 1 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hle : a 1 ≤ A := Finset.le_sup' a hmem
    have h1 : 1 ≤ a 1 := by
      have hget := ha 0
      exact GenContFract.of_one_le_get?_partDen hget
    exact h1.trans hle
  have hpart_le (n : ℕ) (hn : n < N) (b : ℝ)
      (hb : (GenContFract.of τ).partDens.get? n = some b) : b ≤ A := by
    have hget := ha n
    rw [hb] at hget
    have hb_eq : b = a (n + 1) := Option.some_inj.mp hget
    rw [hb_eq]
    exact Finset.le_sup' a (Finset.mem_range.mpr (by omega))
  by_contra! h
  let r := Rat.divInt y x
  have hr : (r : ℝ) = (y : ℝ) / x := by simp [r, Rat.divInt_eq_div]
  have hrq : (r.den : ℝ) ≤ x := by
    exact_mod_cast Int.le_of_dvd hx (Rat.den_dvd y x)
  have hdenpos : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hsmall : |τ - r| < 1 / (2 * (r.den : ℝ) ^ 2) := by
    rw [hr]
    refine h.trans_lt (one_div_lt_one_div_of_lt (mul_pos (by norm_num) (pow_pos hdenpos 2)) ?_)
    calc
      2 * (r.den : ℝ) ^ 2 ≤ 2 * (x : ℝ) ^ 2 := by gcongr
      _ < (A + 2) * (x : ℝ) ^ 2 := mul_lt_mul_of_pos_right (by linarith) (by positivity)
  obtain ⟨n, heq⟩ := Real.exists_convs_eq_rat hsmall
  rw [hr] at heq
  have hD := lt_abs_sub_div_of_max_partialQuotient.den_le_of_convs_eq hinf hx' heq
  have hn : n < N := by
    by_contra! hlt
    exact (not_le_of_gt (lt_trans hxM hqN))
      ((lt_abs_sub_div_of_max_partialQuotient.dens_monotone τ hlt).trans hD)
  have hbound :=
    lt_abs_sub_div_of_max_partialQuotient.convergent_lower_bound (hinf n) (hpart_le n hn)
  rw [heq] at hbound
  have hle : 1 / ((A + 2) * (x : ℝ) ^ 2) ≤
      1 / ((A + 2) * (GenContFract.of τ).dens n ^ 2) := by
    apply one_div_le_one_div_of_le
      (mul_pos (by linarith)
        (pow_pos (lt_abs_sub_div_of_max_partialQuotient.den_pos τ n) 2))
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (lt_abs_sub_div_of_max_partialQuotient.den_pos τ n).le hD 2)
      (by linarith)
  have hAeq : A = (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one a := rfl
  rw [hAeq] at hle
  linarith [hbound, h, hle]

end

end MetaMathlibExt
