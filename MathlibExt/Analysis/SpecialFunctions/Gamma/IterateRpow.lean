/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Gamma.RpowLowerBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Gamma bounds for iterated exponentials

For a base at least e, applying Gamma to a positive iterate of exponentiation
starting from the base gives a value larger than the next exponential iterate.
-/

namespace MetaMathlibExt

open Real

/-- **Gamma of an iterated exponential exceeds the next iterate.** Let $b \ge e$ and, for
$m \ge 0$, let $E_m(b, b)$ be the $m$-fold iterate of $x \mapsto b^x$ started at $b$, so that
$E_0(b, b) = b$ and $E_{m+1}(b, b) = b^{E_m(b, b)}$. Then for every integer $n > 0$,
$E_{n+1}(b, b) < \Gamma(E_n(b, b))$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Lemma 11 (`jis-2025-25.2.8-lem-11`). -/
public theorem iterate_rpow_succ_lt_Gamma_iterate_rpow {b : ℝ} (hb : Real.exp 1 ≤ b)
    {n : ℕ} (hn : 0 < n) :
    (fun x : ℝ => b ^ x)^[n + 1] b < Real.Gamma ((fun x : ℝ => b ^ x)^[n] b) := by
  let f (x : ℝ) := b ^ x
  let x := f^[n] b - 1
  have hb₂ : (5 / 2 : ℝ) ≤ b := by linarith [exp_one_gt_d9]
  have hb₁ : 1 ≤ b := by linarith
  have hb₀ : 0 < b := by positivity
  have hf : Monotone f := fun _ _ huv => rpow_le_rpow_of_exponent_le hb₁ huv
  have hfirst : b ≤ f b := by
    simpa only [f, rpow_one] using hf hb₁
  have hiter : b ^ b ≤ f^[n] b := by
    simpa only [Function.iterate_one, f] using hf.monotone_iterate_of_le_map hfirst hn
  -- Every positive iterate is at least b^(5/2), hence at least (3/2) * b².
  have hroot : (3 / 2 : ℝ) ≤ b ^ (1 / 2 : ℝ) := by
    rw [← sqrt_eq_rpow]
    exact le_sqrt_of_sq_le (by linarith [hb₂])
  have hlarge : (3 / 2 : ℝ) * b ^ 2 ≤ f^[n] b := calc
    _ ≤ b ^ (1 / 2 : ℝ) * b ^ 2 := mul_le_mul_of_nonneg_right hroot (sq_nonneg b)
    _ = b ^ (5 / 2 : ℝ) := by
      rw [← rpow_two, ← rpow_add hb₀]
      norm_num
    _ ≤ b ^ b := rpow_le_rpow_of_exponent_le hb₁ hb₂
    _ ≤ _ := hiter
  have hxlarge : (5 / 4 : ℝ) * b ^ 2 ≤ x := by
    dsimp only [x]
    nlinarith [sq_nonneg (b - 2)]
  have hx : 1 ≤ x := by nlinarith [sq_nonneg (b - 2)]
  have hbase : b * (1 + 1 / 4) ≤ x / exp 1 := by
    apply (le_div_iff₀ (exp_pos 1)).2
    calc
      b * (1 + 1 / 4) * exp 1 ≤ b * (1 + 1 / 4) * b :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (5 / 4 : ℝ) * b ^ 2 := by ring
      _ ≤ x := hxlarge
  have hfactor : b ≤ (1 + 1 / 4 : ℝ) ^ x := calc
    _ ≤ 1 + x * (1 / 4) := by nlinarith [sq_nonneg (b - 2)]
    _ ≤ _ := one_add_mul_self_le_rpow_one_add (by norm_num) hx
  have harg : x + 1 = f^[n] b := sub_add_cancel _ _
  rw [Function.iterate_succ_apply']
  change b ^ (f^[n] b) < Gamma (f^[n] b)
  rw [← harg]
  calc
    b ^ (x + 1) = b ^ x * b := by rw [rpow_add hb₀, rpow_one]
    _ ≤ b ^ x * (1 + 1 / 4) ^ x := mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = (b * (1 + 1 / 4)) ^ x := by rw [mul_rpow hb₀.le (by norm_num)]
    _ ≤ (x / exp 1) ^ x := rpow_le_rpow (by positivity) hbase (zero_le_one.trans hx)
    _ < Gamma (x + 1) := div_exp_one_rpow_lt_Gamma_add_one hx

end MetaMathlibExt
