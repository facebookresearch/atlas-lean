/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity


/-!
# Monotonicity of the exponential harmonic expression

The sequence `exp (harmonic n) * log (harmonic n) / n` is non-decreasing for `n ≥ 1`.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Corollary 3
(`integers-2026-A86-cor-3`).
-/

namespace MetaMathlibExt

@[expose] public section

open Real

private lemma harmonic_cast_succ (n : ℕ) :
    (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + ((n : ℝ) + 1)⁻¹ := by
  simp [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]

private lemma harmonic_bounds (n : ℕ) :
    0 ≤ (harmonic n : ℝ) ∧ (harmonic n : ℝ) ≤ n ∧
      (harmonic n : ℝ) ^ 2 ≤ 2 * n ∧ (1 ≤ n → 1 ≤ (harmonic n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases ih with ⟨h0, hn, hsq, h1⟩
    have hp : 0 < (n : ℝ) + 1 := by positivity
    have ht : 0 ≤ ((n : ℝ) + 1)⁻¹ := (inv_pos.mpr hp).le
    have ht1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      apply (inv_le_one₀ hp).mpr
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have heq : ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
    rw [harmonic_cast_succ, Nat.cast_succ]
    refine ⟨by positivity, by linarith, ?_, ?_⟩
    · have hm := mul_le_mul_of_nonneg_right hn ht
      have ht2 := mul_le_mul_of_nonneg_right ht1 ht
      nlinarith
    · intro _
      cases n with
      | zero => norm_num
      | succ n =>
        have := h1 (Nat.succ_le_succ (Nat.zero_le n))
        linarith

private lemma harmonic_mul_log_le (n : ℕ) (hn : 1 ≤ n) :
    (harmonic n : ℝ) * log (harmonic n : ℝ) ≤ n := by
  rcases harmonic_bounds n with ⟨h0, _, hsq, h1⟩
  have hp : 0 < (harmonic n : ℝ) := lt_of_lt_of_le zero_lt_one (h1 hn)
  have hlog := log_le_sub_one_of_pos (by positivity : 0 < (harmonic n : ℝ) / 2)
  rw [log_div hp.ne' (by norm_num)] at hlog
  have htwo := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hl : log (harmonic n : ℝ) ≤ (harmonic n : ℝ) / 2 := by linarith
  have := mul_le_mul_of_nonneg_left hl h0
  nlinarith

private lemma exp_log_step (x t k : ℝ) (hx : 1 ≤ x) (ht : 0 ≤ t) (hk : 0 < k)
    (htk : t * (k + 1) = 1) (hbound : x * log x ≤ k) :
    exp x * log x / k ≤ exp (x + t) * log (x + t) / (k + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxt : 0 < x + t := by positivity
  have hL : 0 ≤ log x := log_nonneg hx
  have hL' : 0 ≤ log (x + t) := log_nonneg (by linarith)
  have hlog := log_le_sub_one_of_pos (div_pos hx0 hxt)
  rw [log_div hx0.ne' hxt.ne'] at hlog
  have hlog' := (le_div_iff₀ hxt).mp (by linarith : log x - log (x + t) + 1 ≤ x / (x + t))
  have hd : 0 ≤ log (x + t) - log x := by nlinarith
  have hc : x + t ≤ x * (1 + t) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hc hd
  have he := mul_le_mul_of_nonneg_right (add_one_le_exp t) (mul_nonneg hx0.le hL')
  have hinc : x * log x + t * (x * log x + 1) ≤ x * (exp t * log (x + t)) := by
    nlinarith
  have hinc' := mul_le_mul_of_nonneg_left hinc hk.le
  have hb := mul_le_mul_of_nonneg_left hbound ht
  have hfinal : (k + 1) * log x ≤ k * (exp t * log (x + t)) := by
    nlinarith [mul_pos hx0 hk]
  rw [exp_add]
  apply (div_le_div_iff₀ hk (by positivity : 0 < k + 1)).mpr
  have := mul_le_mul_of_nonneg_left hfinal (exp_pos x).le
  nlinarith

/-- **Monotonicity of $e^{H_n} \log H_n / n$.** With $H_n = \sum_{i=1}^n 1/i$ the $n$-th harmonic
number and $\log$ the natural logarithm, the sequence $e^{H_n} \log H_n / n$ is non-decreasing
for $n \ge 1$: its value at $m$ is at most its value at $n$ whenever $1 \le m \le n$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Corollary 3
(`integers-2026-A86-cor-3`). -/
public theorem exp_harmonic_mul_log_div_monotoneOn :
    MonotoneOn (fun n : ℕ => exp (harmonic n : ℝ) * log (harmonic n : ℝ) / n) (Set.Ici 1)
    := by
  apply monotoneOn_nat_Ici_of_le_succ
  intro n hn
  rw [harmonic_cast_succ, Nat.cast_add_one]
  exact exp_log_step (harmonic n) ((n : ℝ) + 1)⁻¹ n ((harmonic_bounds n).2.2.2 hn)
    (by positivity) (by exact_mod_cast hn.trans_lt' Nat.zero_lt_one)
    (inv_mul_cancel₀ (by positivity)) (harmonic_mul_log_le n hn)

end

end MetaMathlibExt
