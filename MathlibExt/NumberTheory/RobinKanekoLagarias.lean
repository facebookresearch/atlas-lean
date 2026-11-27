/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.IntervalCases

/-!
# Robin's inequality implies the Kaneko–Lagarias inequality

For every natural number `n`, if Robin's inequality
`σ(n) < e ^ γ * n * log log n` holds, then the Kaneko–Lagarias inequality
`σ(n) < e ^ H_n * log H_n` holds. The proof compares the two right-hand
sides: the Euler–Mascheroni bounds `H_n - log (n + 1) < γ < H_n - log n`
give `e ^ γ * n < e ^ H_n` and `log log n ≤ log H_n` for `n ≥ 3`, and the
cases `n < 3` are checked directly.
-/

@[expose] public section

open Real

namespace MetaMathlibExt

/-- **Robin's inequality implies the Kaneko–Lagarias inequality.** Let $\sigma(n)$ be the sum of
the divisors of $n$, $\gamma$ the Euler–Mascheroni constant, $\log$ the natural logarithm and
$H_n = 1 + \frac{1}{2} + \cdots + \frac{1}{n}$ the $n$-th harmonic number. For every natural
number $n$, if Robin's inequality $\sigma(n) < e^{\gamma} n \log \log n$ holds, then so does the
Kaneko–Lagarias inequality $\sigma(n) < e^{H_n} \log H_n$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Theorem 10
(`integers-2026-A86-thm-10`). -/
theorem kaneko_lagarias_of_robin (n : ℕ)
    (h : (ArithmeticFunction.sigma 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n)) :
    (ArithmeticFunction.sigma 1 n : ℝ) < exp (harmonic n : ℝ) * log (harmonic n : ℝ) := by
  have hkey : exp eulerMascheroniConstant * n * log (log n) ≤
      exp (harmonic n : ℝ) * log (harmonic n : ℝ) := by
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · simp
      · norm_num [harmonic]
      · have hlog2 : log 2 < 1 := by
          have h := Real.log_two_lt_d9
          linarith
        have hneg : log (log 2) < 0 := by
          rw [← log_one]
          exact log_lt_log (by positivity) hlog2
        have hpos : (0 : ℝ) < exp eulerMascheroniConstant * 2 := by positivity
        have hL : exp eulerMascheroniConstant * (2 : ℝ) * log (log 2) < 0 := by
          have hmul := mul_neg_of_pos_of_neg hpos hneg
          linarith
        have hR : (0 : ℝ) < exp (harmonic 2 : ℝ) * log (harmonic 2 : ℝ) := by
          have hH : (harmonic 2 : ℝ) = 3 / 2 := by norm_num [harmonic]
          rw [hH]
          exact mul_pos (exp_pos _) (log_pos (by norm_num))
        simp only [Nat.cast_ofNat]
        linarith
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hγpos : (0 : ℝ) < eulerMascheroniConstant :=
        lt_trans (by norm_num) one_half_lt_eulerMascheroniConstant
      have hγ : eulerMascheroniConstant < (harmonic n : ℝ) - log n := by
        have hup := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
        simp only [eulerMascheroniSeq', show n ≠ 0 by omega, ↓reduceIte] at hup
        exact hup
      have hHlog : log (n : ℝ) < (harmonic n : ℝ) := by linarith
      have hlogn_pos : (0 : ℝ) < log n := log_pos (by exact_mod_cast (by omega : 1 < n))
      have hlogn_ge1 : (1 : ℝ) ≤ log n := by
        have hexp : exp 1 ≤ (n : ℝ) := by
          have h1 : exp 1 < 2.7182818286 := exp_one_lt_d9
          have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        rw [← log_exp 1]
        exact log_le_log (exp_pos 1) hexp
      have hloglog_nonneg : (0 : ℝ) ≤ log (log n) := by
        rw [← log_one]
        exact log_le_log (by norm_num) hlogn_ge1
      have hexp : exp eulerMascheroniConstant * (n : ℝ) < exp (harmonic n : ℝ) := by
        have heq : exp eulerMascheroniConstant * (n : ℝ) =
            exp (eulerMascheroniConstant + log n) := by
          rw [exp_add, exp_log hn0]
        rw [heq]
        exact exp_lt_exp.mpr (by linarith)
      have hloglog : log (log (n : ℝ)) ≤ log (harmonic n : ℝ) :=
        log_le_log hlogn_pos hHlog.le
      exact mul_le_mul hexp.le hloglog hloglog_nonneg (exp_pos _).le
  exact lt_of_lt_of_le h hkey

end MetaMathlibExt
