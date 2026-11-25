/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import MathlibExt.NumberTheory.Amicable

/-!
# Counting failures of Robin's inequality

The number of integers between `5040` (exclusive) and `x` (inclusive) that fail Robin's
inequality is `O(x / log (log x))`. The proof counts exceptions up to `√x` directly and
bounds the rest using the sum of the abundancy indices `σ(n) / n`.
-/

open Filter Finset Real

namespace MetaMathlibExt

@[expose] public section

/-- **Robin exceptional set.** For a real number $x$, the Robin exceptional set up to $x$ is the
set of natural numbers $n$ with $7! = 5040 < n \le x$ that fail Robin's inequality, that is,
with $\sigma(n) \ge e^\gamma n \log\log n$, where $\sigma(n)$ is the sum of the divisors of $n$
and $\gamma$ is the Euler–Mascheroni constant. Its cardinality is the counting function $N_R(x)$.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Section 1. -/
public noncomputable def robinExceptionalSet (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 5040 ⌊x⌋₊).filter fun n =>
    Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) ≤
      (ArithmeticFunction.sigma 1 n : ℝ)

/-- **The Robin exceptional set is empty up to $7!$.** For every real $x \le 7! = 5040$, the
Robin exceptional set up to $x$ is empty; that is, its cardinality $N_R(x)$ is $0$.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Section 1 (definition of `N_R(x)`). -/
public theorem robinExceptionalSet_eq_empty_of_le {x : ℝ} (hx : x ≤ 5040) :
    robinExceptionalSet x = ∅ := by
  have h : ⌊x⌋₊ ≤ 5040 := Nat.floor_le_of_le (by exact_mod_cast hx)
  simp [robinExceptionalSet, Finset.Ioc_eq_empty_of_le h]

/-- Above the square-root cutoff, a failure contributes at least half of
`log (log x)` to the sum of the abundancy indices. -/
private theorem log_log_le_two_mul_sigma_div {x : ℝ} {n : ℕ}
    (hx : 0 < x) (hlog : 4 ≤ log x) (hcut : √x ≤ n) (hn : n ∈ robinExceptionalSet x) :
    log (log x) ≤ 2 * ((ArithmeticFunction.sigma 1 n : ℝ) / n) := by
  have hlogn := log_le_log (sqrt_pos.2 hx) hcut
  rw [log_sqrt hx.le] at hlogn
  have hn₂ : 2 ≤ log n := by linarith
  have hcomp : log x ≤ (log n) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn₂) (show 0 ≤ log n by linarith)]
  have hlogs := log_le_log (by linarith : 0 < log x) hcomp
  rw [log_pow] at hlogs
  have hfail := (mem_filter.mp hn).2
  have hn₀ : 0 < (n : ℝ) := (sqrt_pos.2 hx).trans_le hcut
  have hγ : 1 ≤ exp eulerMascheroniConstant :=
    one_le_exp (by linarith [one_half_lt_eulerMascheroniConstant])
  have hratio : log (log n) ≤ (ArithmeticFunction.sigma 1 n : ℝ) / n := by
    apply (le_div_iff₀ hn₀).2
    calc
      log (log n) * n ≤ (exp eulerMascheroniConstant * n) * log (log n) := by
        rw [mul_comm (log (log n))]
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hn₀.le hγ)
          (log_nonneg (by linarith))
      _ ≤ _ := hfail
  exact hlogs.trans (by simpa using mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2))

/-- **Failures of Robin's inequality number $O(x/\log\log x)$.** Let $N_R(x)$ be the number of
elements of the Robin exceptional set up to $x$. Then $N_R(x) = O(x / \log\log x)$ as the real
number $x$ tends to infinity.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Theorem 1 (`integers-2025-A8-thm-1`). -/
public theorem card_robinExceptionalSet_isBigO_div_log_log :
    (fun x : ℝ => ((robinExceptionalSet x).card : ℝ)) =O[atTop]
      fun x : ℝ => x / Real.log (Real.log x) := by
  classical
  let Z := ∑' k : ℕ, (1 : ℝ) / (k + 1) ^ 2
  refine Asymptotics.isBigO_iff.mpr ⟨2 + 2 * Z, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), tendsto_log_atTop.eventually_ge_atTop 4]
    with x hx hlog
  have hx₀ : 0 < x := by linarith
  have hll : 0 < log (log x) := log_pos (by linarith)
  let small := (robinExceptionalSet x).filter fun n : ℕ => (n : ℝ) ≤ √x
  let large := (robinExceptionalSet x).filter fun n : ℕ => ¬ (n : ℝ) ≤ √x
  have hsmall : (small.card : ℝ) ≤ √x := by
    have hsub : small ⊆ Ioc 0 ⌊√x⌋₊ := by
      intro n hn
      obtain ⟨hn, hcut⟩ := mem_filter.mp hn
      have hn' := (mem_Ioc.mp (mem_filter.mp hn).1).1
      exact mem_Ioc.mpr ⟨by omega, Nat.le_floor hcut⟩
    have hc := card_le_card hsub
    simp only [Nat.card_Ioc, Nat.sub_zero] at hc
    exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (sqrt_nonneg x))
  have hsmall_sum : (small.card : ℝ) * log (log x) ≤ 2 * x := by
    have hll' : log (log x) ≤ 2 * √x := by
      linarith [log_le_self (show 0 ≤ log x by linarith), log_le_self (sqrt_nonneg x),
        log_sqrt hx₀.le]
    calc
      _ ≤ √x * (2 * √x) := mul_le_mul hsmall hll' hll.le (sqrt_nonneg x)
      _ = _ := by nlinarith [sq_sqrt hx₀.le]
  have hlarge_sum : (large.card : ℝ) * log (log x) ≤ 2 * (Z * x) := calc
    _ = ∑ _n ∈ large, log (log x) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ large, 2 * ((ArithmeticFunction.sigma 1 n : ℝ) / n) := by
      refine sum_le_sum fun n hn => ?_
      obtain ⟨hn, hcut⟩ := mem_filter.mp hn
      exact log_log_le_two_mul_sigma_div hx₀ hlog (le_of_not_ge hcut) hn
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, 2 * ((ArithmeticFunction.sigma 1 n : ℝ) / n) := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
      intro n hn
      obtain ⟨hlo, hhi⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hn).1).1
      exact mem_Icc.mpr ⟨by omega, hhi⟩
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (MathlibExt.NumberTheory.AmicableWanted.sum_sigma_div_lt x hx).le (by norm_num)
  have hcard : small.card + large.card = (robinExceptionalSet x).card :=
    card_filter_add_card_filter_not _
  simp only [Real.norm_eq_abs, Nat.abs_cast, abs_of_nonneg (div_nonneg hx₀.le hll.le)]
  rw [← mul_div_assoc, le_div_iff₀ hll, ← hcard, Nat.cast_add, add_mul]
  linarith

end

end MetaMathlibExt
