/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MotzkinAlternatingSums
import all MathlibExt.Combinatorics.Enumerative.MotzkinAlternatingSums
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Products of consecutive alternating Motzkin sums

The products satisfy the log-convexity inequality from index 7 and the log-balance
inequalities from index 10.
-/

namespace MetaMathlibExt

namespace motzkinAlternatingSum_mul_succ_logConvex_logBalanced

open motzkinAlternatingSum_logBalanced_tempered

private abbrev P (n : ℕ) : ℤ := motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)

private lemma nonneg (k : ℕ) (hk : 8 ≤ k) : 0 ≤ T k := by
  have := (bounds k hk).1
  omega

private lemma product_bounds (k : ℕ) (hk : 8 ≤ k) :
    P (k + 1) ^ 2 ≤ P k * P (k + 2) ∧
      (k + 1 : ℤ) * (P k * P (k + 2)) ≤ (k + 2 : ℤ) * P (k + 1) ^ 2 := by
  have ha := nonneg k hk
  have hb := nonneg (k + 1) (by omega)
  have hc := nonneg (k + 2) (by omega)
  have hd := nonneg (k + 3) (by omega)
  constructor
  · -- Multiply the log-convexity inequalities at the two consecutive indices.
    have h := mul_le_mul (tail k hk).1 (tail (k + 1) (by omega)).1
      (sq_nonneg _) (mul_nonneg ha hc)
    change (T (k + 1) * T (k + 2)) ^ 2 ≤ (T k * T (k + 1)) * (T (k + 2) * T (k + 3))
    linear_combination h
  · -- Compare the upper ratio bound at k + 2 with the lower one at k.
    have hl := (bounds k hk).2.1
    have hu := (bounds (k + 2) (by omega)).2.2
    push_cast at hu
    have hgap : (k + 4 : ℤ) * (2 * k + 5) ≤ (k + 2 : ℤ) * (2 * k + 11) := by
      nlinarith only [Nat.cast_nonneg (α := ℤ) k]
    have h : (k + 1 : ℤ) * (T k * T (k + 3)) ≤ (k + 2 : ℤ) * (T (k + 1) * T (k + 2)) := by
      apply le_of_mul_le_mul_left (a := 6 * (2 * (k : ℤ) + 11)) _ (by positivity)
      linear_combination (2 * (k : ℤ) + 11) * T (k + 3) * hl +
        (2 * (k : ℤ) + 5) * T (k + 1) * hu + 6 * T (k + 1) * T (k + 2) * hgap
    change (k + 1 : ℤ) * ((T k * T (k + 1)) * (T (k + 2) * T (k + 3))) ≤
      (k + 2 : ℤ) * (T (k + 1) * T (k + 2)) ^ 2
    linear_combination T (k + 1) * T (k + 2) * h

end motzkinAlternatingSum_mul_succ_logConvex_logBalanced

open motzkinAlternatingSum_mul_succ_logConvex_logBalanced in
/-- **Products of consecutive alternating Motzkin sums are eventually log-convex and
log-balanced.** Let $M_k$ denote the $k$-th Motzkin number, let
$T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$ and let $P_n = T_n T_{n+1}$. For every natural number
$n \ge 7$, $P_n^2 \le P_{n-1} P_{n+1}$; and for every natural number $n \ge 10$,
$P_n^2 \le P_{n-1} P_{n+1}$ and $n P_{n-1} P_{n+1} \le (n+1) P_n^2$.

Following Došlić, a positive sequence $(z_n)_{n \ge N}$ is log-convex if
$z_n^2 \le z_{n-1} z_{n+1}$ for every $n \ge N + 1$, and log-balanced if moreover $(z_n/n!)$ is
log-concave, $n z_{n-1} z_{n+1} \le (n+1) z_n^2$, for every $n \ge N + 1$. So the two parts say
that $(P_n)_{n \ge 6}$ is log-convex and $(P_n)_{n \ge 9}$ is log-balanced.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 2. -/
public theorem motzkinAlternatingSum_mul_succ_logConvex_logBalanced :
    (∀ n, 7 ≤ n →
      (motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)) ^ 2 ≤
        (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum n) *
          (motzkinAlternatingSum (n + 1) * motzkinAlternatingSum (n + 2))) ∧
    (∀ n, 10 ≤ n →
      (motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)) ^ 2 ≤
          (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum n) *
            (motzkinAlternatingSum (n + 1) * motzkinAlternatingSum (n + 2)) ∧
        n * ((motzkinAlternatingSum (n - 1) * motzkinAlternatingSum n) *
            (motzkinAlternatingSum (n + 1) * motzkinAlternatingSum (n + 2))) ≤
          (n + 1) * (motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)) ^ 2) := by
  constructor <;> intro n hn <;>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  · by_cases hk : 8 ≤ k
    · exact (product_bounds k hk).1
    · have : 6 ≤ k := by omega
      interval_cases k <;>
        simp only [motzkinAlternatingSum, motzkinNumber_eq_sum_range_half,
          catalan_eq_centralBinom_div] <;> decide
  · simpa [add_assoc] using product_bounds k (by omega)

end MetaMathlibExt
