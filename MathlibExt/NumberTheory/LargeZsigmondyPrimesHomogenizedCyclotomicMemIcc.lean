/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomic

import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Bounds for homogenized cyclotomic values

For integers `a > b > 0` and `n ≥ 1`, the homogenized cyclotomic value `Φₙ(a, b)` lies
between `(a - b)^φ(n)` and `(a + b)^φ(n)`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (ii)
(quoted from reference [6]).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Bounds for homogenized cyclotomic values.** Let $a > b$ be positive integers and let
$n \ge 1$. Then the homogenized cyclotomic value $\Phi_n(a, b)$ satisfies
$(a - b)^{\varphi(n)} \le \Phi_n(a, b) \le (a + b)^{\varphi(n)}$, where $\varphi$ is Euler's
totient function.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (ii)
(quoted from reference [6]). -/
public theorem homogenizedCyclotomic_mem_Icc {a b n : ℕ} (hb : 0 < b) (hba : b < a)
    (hn : 0 < n) :
    ((a : ℤ) - b) ^ Nat.totient n ≤ homogenizedCyclotomic n a b ∧
      homogenizedCyclotomic n a b ≤ ((a : ℤ) + b) ^ Nat.totient n
    := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hba' : (b : ℝ) < a := by exact_mod_cast hba
  have hq : (1 : ℝ) < a / b := (one_lt_div hb').2 hba'
  have hpow : (0 : ℝ) ≤ (b : ℝ) ^ Nat.totient (n + 1) := pow_nonneg hb'.le _
  have hlo := mul_le_mul_of_nonneg_left
    (Polynomial.sub_one_pow_totient_le_cyclotomic_eval hq (n + 1)) hpow
  have hhi := mul_le_mul_of_nonneg_left
    (Polynomial.cyclotomic_eval_le_add_one_pow_totient hq (n + 1)) hpow
  have hsub : (b : ℝ) * (a / b - 1) = a - b := by
    rw [mul_sub, mul_div_cancel₀ _ hb'.ne', mul_one]
  have hadd : (b : ℝ) * (a / b + 1) = a + b := by
    rw [mul_add, mul_div_cancel₀ _ hb'.ne', mul_one]
  have hcast := homogenizedCyclotomic_cast (K := ℝ) (n + 1) (a : ℤ) (b : ℤ)
    (by exact_mod_cast hb'.ne')
  push_cast at hcast
  rw [← hcast, ← mul_pow, hsub] at hlo
  rw [← hcast, ← mul_pow, hadd] at hhi
  exact_mod_cast And.intro hlo hhi

end

end MetaMathlibExt
