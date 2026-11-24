/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Analysis.SpecialFunctions.LambertWFunction

/-!
# A lower bound for the Lambert sequence

We prove `two_mul_sub_four_lt_lambertSequence`, a strict linear lower bound for the
sequence defined by the lower real branch of the Lambert W function.
-/

namespace MetaMathlibExt

open Real

/-- **A linear lower bound for the Lambert sequence.** Let $n \ge 4$ be a natural number, write
$h(y) = y e^y$ for the Lambert map, and let $a$ be a real number with $a \ge n - 1$ such that

$$h\left(-\frac{a}{n - 1}\right) = -\frac{1}{n - 1} \left(\frac{4}{7}\right)^{1/(n - 1)}.$$

Then $2n - 4 < \frac{3}{4} a$.

These conditions determine $a$ uniquely: it is the paper's
$a_n = -(n - 1) W_{-1}\bigl(-\frac{1}{n - 1} (4/7)^{1/(n - 1)}\bigr)$, where $W_{-1}$ is the lower
real branch of the Lambert W function.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Lemma 8 (`jis-2024-24.5.7-lem-8`). -/
public theorem two_mul_sub_four_lt_lambertSequence (n : ℕ) (hn : 4 ≤ n)
    (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    2 * (n : ℝ) - 4 < 3 / 4 * a := by
  let d : ℝ := (n : ℝ) - 1
  let b : ℝ := (8 / 3 : ℝ) * ((n : ℝ) - 2)
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < d := by dsimp [d]; linarith
  have he₂ : exp 2 < 15 / 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    exact (mul_self_lt_mul_self (exp_pos 1).le exp_one_lt_d9).trans (by norm_num)
  -- Bound the rescaled Lambert target at the proposed cutoff.
  have hcut : (4 / 7 : ℝ) ^ (1 / d) * exp (b / d) < b := by
    by_cases h : n = 4
    · subst n
      have hd₄ : d = 3 := by norm_num [d]
      have hb₄ : b = 16 / 3 := by norm_num [b]
      rw [hd₄, hb₄, show (16 / 3 : ℝ) / 3 = 16 / 9 by norm_num]
      have hroot : (4 / 7 : ℝ) ^ (1 / 3 : ℝ) < 5 / 6 := by
        rw [one_div]
        calc
          _ < ((5 / 6 : ℝ) ^ (3 : ℕ)) ^ ((3 : ℝ)⁻¹) :=
            rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
          _ = _ := pow_rpow_inv_natCast (by norm_num) (by decide : (3 : ℕ) ≠ 0)
      have he : exp (16 / 9) < 25 / 4 := by
        rw [show (16 / 9 : ℝ) = 2 + -(2 / 9) by norm_num, exp_add, exp_neg,
          ← div_eq_mul_inv, div_lt_iff₀ (exp_pos _)]
        linarith [add_one_le_exp (2 / 9 : ℝ)]
      calc
        _ < (5 / 6 : ℝ) * (25 / 4) := by
          exact mul_lt_mul hroot he.le (exp_pos _) (by norm_num)
        _ < _ := by norm_num
    · have hn₅ : (5 : ℝ) ≤ n := by exact_mod_cast (show 5 ≤ n by omega)
      have hz₀ : 0 ≤ b / d - 2 := by
        rw [sub_nonneg, le_div_iff₀ hd]
        dsimp [b, d]
        linarith
      have hz₁ : b / d - 2 < 1 := by
        have : b / d < 3 := (div_lt_iff₀ hd).mpr (by dsimp [b, d]; linarith)
        linarith
      have he : exp (b / d) < b := calc
        exp (b / d) = exp 2 * exp (b / d - 2) := by
          rw [← exp_add, show 2 + (b / d - 2) = b / d by ring]
        _ < 8 * exp (b / d - 2) :=
          mul_lt_mul_of_pos_right (he₂.trans (by norm_num)) (exp_pos _)
        _ ≤ 8 * (1 / (1 - (b / d - 2))) :=
          mul_le_mul_of_nonneg_left (exp_bound_div_one_sub_of_interval hz₀ hz₁) (by norm_num)
        _ ≤ b := by
          rw [mul_one_div, div_le_iff₀ (sub_pos.mpr hz₁)]
          apply (mul_le_mul_iff_of_pos_right hd).mp
          rw [show b * (1 - (b / d - 2)) * d = b * (3 * d - b) by
            field_simp [hd.ne']
            ring]
          dsimp [b, d]
          nlinarith [sq_nonneg ((n : ℝ) - 5)]
      exact (mul_le_of_le_one_left (exp_pos _).le
        (rpow_le_one (by norm_num) (by norm_num) (by positivity))).trans_lt he
  have ha' : d ≤ a := ha
  have hWa : a = (4 / 7 : ℝ) ^ (1 / d) * exp (a / d) := by
    change (-a / d) * exp (-a / d) = -(1 / d) * (4 / 7 : ℝ) ^ (1 / d) at hW
    rw [neg_div, exp_neg, neg_mul, neg_mul, neg_inj, ← div_eq_mul_inv,
      div_eq_iff (exp_ne_zero _)] at hW
    calc
      a = (a / d) * d := (div_mul_cancel₀ _ hd.ne').symm
      _ = ((1 / d) * (4 / 7 : ℝ) ^ (1 / d) * exp (a / d)) * d := congrArg (· * d) hW
      _ = _ := by field_simp [hd.ne']
  suffices b < a by
    dsimp [b] at this
    linarith
  by_contra! hab
  -- For d ≤ a ≤ b, the inequality 1 + x ≤ exp x gives the lower-branch comparison.
  have huv : 0 ≤ b / d - a / d := sub_nonneg.mpr (div_le_div_of_nonneg_right hab hd.le)
  have hcmp : b ≤ a * exp (b / d - a / d) := calc
    b ≤ a * ((b / d - a / d) + 1) := by
      have hdif : d * (b / d - a / d) = b - a := by field_simp [hd.ne']
      nlinarith [mul_nonneg (sub_nonneg.mpr ha') huv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_one_le_exp _) (hd.le.trans ha')
  rw [exp_sub, ← mul_div_assoc, le_div_iff₀ (exp_pos _)] at hcmp
  have hscaled : b * exp (a / d) ≤ ((4 / 7 : ℝ) ^ (1 / d) * exp (b / d)) * exp (a / d) :=
    calc
      _ ≤ a * exp (b / d) := hcmp
      _ = ((4 / 7 : ℝ) ^ (1 / d) * exp (a / d)) * exp (b / d) :=
        congrArg (· * exp (b / d)) hWa
      _ = _ := by ring
  exact (not_lt_of_ge ((mul_le_mul_iff_of_pos_right (exp_pos _)).mp hscaled)) hcut

end MetaMathlibExt
