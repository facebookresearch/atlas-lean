/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.LambertWFunction
public import MathlibExt.NumberTheory.GoldenFactorialExponent
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# The golden factorial exponent exceeds the Lambert sequence

We prove that every lower-branch Lambert witness at an index greater than four is
strictly smaller than the golden factorial exponent.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 6 (`jis-2024-24.5.7-thm-6`).
-/

namespace MetaMathlibExt

open Real

private theorem goldenRatio_lt_bound : goldenRatio < 16181 / 10000 := by
  nlinarith [goldenRatio_sq, one_lt_goldenRatio]

private theorem log_goldenRatio_lt_half : log goldenRatio < 1 / 2 := by
  rw [log_lt_iff_lt_exp goldenRatio_pos]
  have he : (16181 / 10000 : ℝ) ^ 2 < exp 1 := by
    linarith [exp_one_gt_d9]
  have heq : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by
    rw [← exp_nat_mul]
    norm_num
  nlinarith [goldenRatio_lt_bound, exp_pos (1 / 2 : ℝ)]

private theorem exponent_ge_of_pow_lt (n m : ℕ) (hm : 0 < m)
    (hpow : (16181 / 10000 : ℝ) ^ (m - 1) < n.factorial) :
    m ≤ goldenFactorialExponent n := by
  by_contra! h
  have hle : goldenFactorialExponent n ≤ m - 1 := by omega
  have hsmall := (goldenFactorialExponent_mem n).2
  have hbound := pow_le_pow_right₀ one_lt_goldenRatio.le hle
  have hr := pow_le_pow_left₀ goldenRatio_pos.le goldenRatio_lt_bound.le (m - 1)
  exact (not_lt_of_ge (hsmall.trans (hbound.trans hr))) hpow

private theorem cutoff_of_pow_lt (n m : ℕ) (hn : 1 < n)
    (hp : (7 / 4 : ℝ) * (m : ℝ) ^ (n - 1) < (2718 / 1000 : ℝ) ^ m) :
    (m : ℝ) < (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) *
      exp ((m : ℝ) / ((n : ℝ) - 1)) := by
  have hd : 0 < (n : ℝ) - 1 := by
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  have he : (2718 / 1000 : ℝ) ^ m ≤ exp (m : ℝ) := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718 / 1000)
      (show (2718 / 1000 : ℝ) ≤ exp 1 by linarith [exp_one_gt_d9]) m
    simpa only [← exp_nat_mul, mul_one] using this
  have hp' : (m : ℝ) ^ (n - 1) < (4 / 7 : ℝ) * exp (m : ℝ) := by
    linarith [hp.trans_le he]
  have hroot := rpow_lt_rpow (by positivity : 0 ≤ (m : ℝ) ^ (n - 1)) hp'
    (one_div_pos.mpr hd)
  rw [← hcast, one_div, pow_rpow_inv_natCast (by positivity) (by omega)] at hroot
  rw [mul_rpow (by norm_num) (exp_pos _).le, ← exp_mul] at hroot
  simpa only [hcast, ← div_eq_mul_inv, one_div] using hroot

private theorem lt_of_cutoff (n : ℕ) (hn : 1 < n) (a b : ℝ)
    (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)))
    (hb : (n : ℝ) - 1 ≤ b)
    (hcut : b < (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) *
      exp (b / ((n : ℝ) - 1))) : a < b := by
  let d : ℝ := (n : ℝ) - 1
  have hd : 0 < d := by
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    dsimp [d]
    linarith
  have ha0 : 0 ≤ a := hd.le.trans ha
  have hWa : a = (4 / 7 : ℝ) ^ (1 / d) * exp (a / d) := by
    change (-a / d) * exp (-a / d) = -(1 / d) * (4 / 7 : ℝ) ^ (1 / d) at hW
    rw [neg_div, exp_neg, neg_mul, neg_mul, neg_inj, ← div_eq_mul_inv,
      div_eq_iff (exp_ne_zero _)] at hW
    calc
      a = (a / d) * d := (div_mul_cancel₀ _ hd.ne').symm
      _ = ((1 / d) * (4 / 7 : ℝ) ^ (1 / d) * exp (a / d)) * d := congrArg (· * d) hW
      _ = _ := by field_simp [hd.ne']
  by_contra! hab
  have huv : 0 ≤ a / d - b / d := sub_nonneg.mpr (div_le_div_of_nonneg_right hab hd.le)
  have hcmp : a ≤ b * exp (a / d - b / d) := calc
    a ≤ b * ((a / d - b / d) + 1) := by
      have hdif : d * (a / d - b / d) = a - b := by field_simp [hd.ne']
      nlinarith [mul_nonneg (sub_nonneg.mpr hb) huv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_one_le_exp _) (hd.le.trans hb)
  rw [exp_sub, ← mul_div_assoc, le_div_iff₀ (exp_pos _)] at hcmp
  have hscaled : ((4 / 7 : ℝ) ^ (1 / d) * exp (b / d)) * exp (a / d) ≤
      b * exp (a / d) := calc
    _ = a * exp (b / d) := by
      conv_rhs => rw [hWa]
      ring
    _ ≤ _ := hcmp
  exact (not_lt_of_ge ((mul_le_mul_iff_of_pos_right (exp_pos _)).mp hscaled)) hcut

private theorem large_cutoff (n : ℕ) (hn : 32 ≤ n) :
    let b : ℝ := 2 * (n : ℝ) * (log n - 1) + 2
    (n : ℝ) - 1 ≤ b ∧ b < goldenFactorialExponent n ∧
      b < (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) * exp (b / ((n : ℝ) - 1)) := by
  let q : ℝ := n
  let d : ℝ := q - 1
  let L : ℝ := log q
  let b : ℝ := 2 * q * (L - 1) + 2
  have hq : 32 ≤ q := by
    dsimp [q]
    exact_mod_cast hn
  have hq0 : 0 < q := by linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hl32 : log (32 : ℝ) = 5 * log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, log_pow]
    norm_num
  have hL : 3 ≤ L := by
    have := log_le_log (by norm_num : (0 : ℝ) < 32) hq
    dsimp [L] at *
    rw [hl32] at this
    linarith [log_two_gt_d9]
  have hLu : L ≤ q / 32 + 5 / 2 := by
    have := log_le_sub_one_of_pos (div_pos hq0 (by norm_num : (0 : ℝ) < 32))
    rw [log_div hq0.ne' (by norm_num), hl32] at this
    dsimp [L]
    linarith [log_two_lt_d9]
  have hb : d ≤ b := by dsimp [d, b]; nlinarith
  have hf : q * L - q + 1 ≤ log (n.factorial : ℝ) := by
    have := Stirling.le_log_factorial_stirling (show n ≠ 0 by omega)
    have hp : 0 ≤ log (2 * π) := log_nonneg (by linarith [two_le_pi])
    change q * L - q + L / 2 + log (2 * π) / 2 ≤ _ at this
    linarith
  have hbexp : b < goldenFactorialExponent n := by
    have hm : (0 : ℝ) < goldenFactorialExponent n := by
      exact_mod_cast (goldenFactorialExponent_mem n).1
    have hlog := log_le_log (by positivity : (0 : ℝ) < n.factorial)
      (goldenFactorialExponent_mem n).2
    rw [log_pow] at hlog
    have hphi := mul_lt_mul_of_pos_left log_goldenRatio_lt_half hm
    dsimp [b]
    linarith
  have hc : (49 / 50 : ℝ) ≤ (4 / 7 : ℝ) ^ (1 / d) := by
    have hcast : ((n - 1 : ℕ) : ℝ) = d := by
      dsimp [d, q]
      simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
    have hp : (49 / 50 : ℝ) ^ (n - 1) ≤ 4 / 7 := calc
      _ ≤ (49 / 50 : ℝ) ^ (31 : ℕ) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ _ := by norm_num
    have hr := rpow_le_rpow (by positivity : 0 ≤ (49 / 50 : ℝ) ^ (n - 1)) hp
      (one_div_pos.mpr hd).le
    rw [← hcast, one_div, pow_rpow_inv_natCast (by norm_num) (by omega)] at hr
    simpa only [hcast, one_div] using hr
  have he₂ : exp 2 < 37 / 5 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_pos 1]
  have hpoly : b < (49 / 370 : ℝ) * q ^ 2 * (1 + 2 * L / d) := by
    have hcoef : 0 ≤ 642 * q ^ 2 - 740 * q := by nlinarith
    have htangent := mul_nonneg hcoef (sub_nonneg.mpr hLu)
    have hcube := mul_nonneg (sq_nonneg q)
      (show 0 ≤ 463 / 16 * q - 7127 / 8 by linarith)
    have h : 370 * b * d < 49 * q ^ 2 * (d + 2 * L) := by
      dsimp [b, d] at *
      nlinarith
    apply (mul_lt_mul_iff_of_pos_right hd).mp
    convert (show b * d < (49 / 370 : ℝ) * q ^ 2 * (d + 2 * L) by linarith) using 1
    field_simp [hd.ne']
  have hbd : b / d = (2 * L - 2) + 2 * L / d := by
    apply (div_eq_iff hd.ne').mpr
    field_simp [hd.ne']
    dsimp [b, d]
    ring
  have hexp : exp (b / d) = (q ^ 2 / exp 2) * exp (2 * L / d) := by
    rw [hbd, exp_add, exp_sub]
    have h : exp (2 * L) = q ^ 2 := by
      dsimp [L]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by rfl, exp_nat_mul, exp_log hq0]
    rw [h]
  have hcut : b < (4 / 7 : ℝ) ^ (1 / d) * exp (b / d) := calc
    b < (49 / 370 : ℝ) * q ^ 2 * (1 + 2 * L / d) := hpoly
    _ = (49 / 50 : ℝ) * (q ^ 2 / (37 / 5)) * (1 + 2 * L / d) := by ring
    _ ≤ (49 / 50 : ℝ) * (q ^ 2 / exp 2) * (1 + 2 * L / d) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (sq_nonneg q) (exp_pos 2) he₂.le) (by norm_num))
        (by positivity)
    _ ≤ (49 / 50 : ℝ) * (q ^ 2 / exp 2) * exp (2 * L / d) :=
      mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp (2 * L / d)]) (by positivity)
    _ ≤ (4 / 7 : ℝ) ^ (1 / d) * (q ^ 2 / exp 2) * exp (2 * L / d) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by positivity)) (exp_pos _).le
    _ = _ := by rw [hexp]; ring
  exact ⟨hb, hbexp, hcut⟩

private theorem small_cutoff_aux (n m : ℕ) (hn : 1 < n) (hm : 0 < m)
    (hb : (n : ℝ) - 1 ≤ m)
    (hpow : (16181 / 10000 : ℝ) ^ (m - 1) < n.factorial)
    (hp : (7 / 4 : ℝ) * (m : ℝ) ^ (n - 1) < (2718 / 1000 : ℝ) ^ m) :
    ∃ b : ℝ, (n : ℝ) - 1 ≤ b ∧ b ≤ goldenFactorialExponent n ∧
      b < (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) * exp (b / ((n : ℝ) - 1)) := by
  refine ⟨m, hb, ?_, cutoff_of_pow_lt n m hn hp⟩
  exact_mod_cast exponent_ge_of_pow_lt n m hm hpow

private theorem small_cutoff (n : ℕ) (hn : 4 < n) (h32 : n < 32) :
    ∃ b : ℝ, (n : ℝ) - 1 ≤ b ∧ b ≤ goldenFactorialExponent n ∧
      b < (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) * exp (b / ((n : ℝ) - 1)) := by
  interval_cases n
  · exact small_cutoff_aux 5 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 6 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 7 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 8 23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 9 27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 10 32 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 11 37 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 12 42 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 13 47 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 14 53 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 15 58 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 16 64 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 17 70 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 18 76 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 19 82 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 20 88 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 21 95 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 22 101 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 23 108 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 24 114 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 25 121 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 26 128 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 27 135 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 28 142 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 29 149 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 30 156 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact small_cutoff_aux 31 163 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

@[expose] public section

/-- **The golden factorial exponent exceeds the Lambert sequence.** Let $n > 4$ be an integer, let
$h(y) = y e^y$ be the Lambert map, and let $a$ be a real number with $a \ge n - 1$ and
$$h\left(-\frac{a}{n-1}\right) = -\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}.$$
Then $a < \alpha(n)$, where $\alpha(n)$ is the least positive integer $m$ with $n! \le \varphi^m$
and $\varphi$ is the golden ratio.

The two conditions on $a$ say exactly that
$a = -(n-1)\, W_{-1}\left(-\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}\right)$, where $W_{-1}$
is the lower real branch of the Lambert $W$ function; this is the paper's $a(n)$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 6 (`jis-2024-24.5.7-thm-6`). -/
public theorem lambertSequence_lt_goldenFactorialExponent (n : ℕ) (hn : 4 < n)
    (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    a < goldenFactorialExponent n
    := by
  by_cases h32 : n < 32
  · obtain ⟨b, hb, hbexp, hcut⟩ := small_cutoff n hn h32
    exact (lt_of_cutoff n (by omega) a b ha hW hb hcut).trans_le hbexp
  · obtain ⟨hb, hbexp, hcut⟩ := large_cutoff n (by omega)
    exact (lt_of_cutoff n (by omega) a _ ha hW hb hcut).trans hbexp

end

end MetaMathlibExt
