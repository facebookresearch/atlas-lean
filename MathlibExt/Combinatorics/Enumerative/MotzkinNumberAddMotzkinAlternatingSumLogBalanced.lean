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
# Log-balancedness of Motzkin numbers plus their alternating sums

The sequence $z_n = M_n + T_n$, the sum of the $n$-th Motzkin number and the $n$-th
alternating Motzkin sum, is log-balanced from index $6$: for every $n \ge 7$,
$z_n^2 \le z_{n-1} z_{n+1}$ and $n z_{n-1} z_{n+1} \le (n+1) z_n^2$.
-/

namespace MetaMathlibExt

@[expose] public section

namespace motzkinNumber_add_motzkinAlternatingSum_logBalanced

open motzkinAlternatingSum_logBalanced_tempered

/-- Propagate the ratio bounds for Motzkin numbers through one step of the
Motzkin recurrence. -/
private lemma motzkinNumber_bounds_step {k x y z : ℤ} (hk : 1 ≤ k)
    (hr : (k + 4) * z = (2 * k + 5) * y + 3 * (k + 1) * x)
    (hl : (6 * k + 6) * x ≤ (2 * k + 5) * y)
    (hu : (2 * k + 7) * y ≤ (6 * k + 12) * x) :
    (6 * k + 12) * y ≤ (2 * k + 7) * z ∧ (2 * k + 9) * z ≤ (6 * k + 18) * y := by
  constructor
  · apply le_of_mul_le_mul_left (a := 2 * (k + 4)) _ (by linarith)
    linear_combination (k - 1) * hl + 3 * (k + 1) * hu - 2 * (2 * k + 7) * hr
  · apply le_of_mul_le_mul_left (a := 2 * (k + 4)) _ (by linarith)
    linear_combination (5 * k + 15) * hl + (3 * k + 3) * hu + 2 * (2 * k + 9) * hr

/-- The quotient `M (n + 1) / M n` of consecutive Motzkin numbers lies between
`(6n + 6) / (2n + 5)` and `(6n + 12) / (2n + 7)`, the same bounds as for the
alternating sums. -/
private lemma motzkinNumber_bounds (n : ℕ) (hn : 1 ≤ n) :
    (6 * (n : ℤ) + 6) * (motzkinNumber n : ℤ) ≤
        (2 * (n : ℤ) + 5) * (motzkinNumber (n + 1) : ℤ) ∧
      (2 * (n : ℤ) + 7) * (motzkinNumber (n + 1) : ℤ) ≤
        (6 * (n : ℤ) + 12) * (motzkinNumber n : ℤ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num [motzkinNumber_one, motzkinNumber_two]
  | succ n hn ih =>
    obtain ⟨hl, hu⟩ := ih
    have hr := motzkin_step n
    push_cast at hr ⊢
    have hk : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    obtain ⟨hl', hu'⟩ := motzkinNumber_bounds_step hk hr hl hu
    exact ⟨by linear_combination hl', by linear_combination hu'⟩

/-- The sums `M n + T n` satisfy the same ratio bounds as their two summands. -/
private lemma sum_bounds (k : ℕ) (hk : 8 ≤ k) :
    (6 * (k : ℤ) + 6) * ((motzkinNumber k : ℤ) + motzkinAlternatingSum k) ≤
        (2 * (k : ℤ) + 5) *
          ((motzkinNumber (k + 1) : ℤ) + motzkinAlternatingSum (k + 1)) ∧
      (2 * (k : ℤ) + 7) *
          ((motzkinNumber (k + 1) : ℤ) + motzkinAlternatingSum (k + 1)) ≤
        (6 * (k : ℤ) + 12) * ((motzkinNumber k : ℤ) + motzkinAlternatingSum k) := by
  have hM := motzkinNumber_bounds k (by omega)
  have hT := (bounds k hk).2
  constructor
  · linear_combination hM.1 + hT.1
  · linear_combination hM.2 + hT.2

/-- The sums `M n + T n` are nonnegative from index 8. -/
private lemma sum_nonneg (k : ℕ) (hk : 8 ≤ k) :
    0 ≤ (motzkinNumber k : ℤ) + motzkinAlternatingSum k := by
  have hT : 0 ≤ motzkinAlternatingSum k := by
    have h : 8 * (2 * (k : ℤ) + 9) ≤ motzkinAlternatingSum k := (bounds k hk).1
    omega
  have hM : 0 ≤ (motzkinNumber k : ℤ) := by exact_mod_cast Nat.zero_le _
  linarith

/-- The tail inequalities for the sums `M n + T n`, proved from the ratio
bounds at three consecutive indices as for the alternating sums. -/
private lemma sum_tail (k : ℕ) (hk : 8 ≤ k) :
    ((motzkinNumber (k + 1) : ℤ) + motzkinAlternatingSum (k + 1)) ^ 2 ≤
        ((motzkinNumber k : ℤ) + motzkinAlternatingSum k) *
          ((motzkinNumber (k + 2) : ℤ) + motzkinAlternatingSum (k + 2)) ∧
      (k + 1 : ℤ) * (((motzkinNumber k : ℤ) + motzkinAlternatingSum k) *
          ((motzkinNumber (k + 2) : ℤ) + motzkinAlternatingSum (k + 2))) ≤
        (k + 2 : ℤ) * ((motzkinNumber (k + 1) : ℤ) +
          motzkinAlternatingSum (k + 1)) ^ 2 := by
  obtain ⟨hl, hu⟩ := sum_bounds k hk
  obtain ⟨hl', hu'⟩ := sum_bounds (k + 1) (by omega)
  have hx₀ := sum_nonneg k hk
  have hy₀ := sum_nonneg (k + 1) (by omega)
  have hz₀ := sum_nonneg (k + 2) (by omega)
  push_cast at hl' hu'
  constructor
  · apply le_of_mul_le_mul_left (a := 2 * (k : ℤ) + 7) _ (by positivity)
    linear_combination
      ((motzkinNumber (k + 1) : ℤ) + motzkinAlternatingSum (k + 1)) * hu +
        ((motzkinNumber k : ℤ) + motzkinAlternatingSum k) * hl'
  · apply le_of_mul_le_mul_left (a := 6 * (2 * (k : ℤ) + 9)) _ (by positivity)
    have hgap : ((k : ℤ) + 3) * (2 * k + 5) ≤ (k + 2 : ℤ) * (2 * k + 9) := by
      nlinarith only [Nat.cast_nonneg (α := ℤ) k]
    linear_combination (2 * (k : ℤ) + 9) *
        ((motzkinNumber (k + 2) : ℤ) + motzkinAlternatingSum (k + 2)) * hl +
        (2 * (k : ℤ) + 5) * ((motzkinNumber (k + 1) : ℤ) +
          motzkinAlternatingSum (k + 1)) * hu' +
        6 * ((motzkinNumber (k + 1) : ℤ) + motzkinAlternatingSum (k + 1)) ^ 2 * hgap

end motzkinNumber_add_motzkinAlternatingSum_logBalanced

/-- **Log-balancedness of Motzkin numbers plus their alternating sums.** Let $M_n$ denote the
$n$-th Motzkin number, let $T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$ be the alternating sum of
Motzkin numbers, and put $z_n = M_n + T_n$. Then the sequence $(z_n)_{n \ge 6}$ is log-balanced:
for every natural number $n \ge 7$,
$$z_n^2 \le z_{n-1} \, z_{n+1} \quad\text{and}\quad n \, z_{n-1} \, z_{n+1} \le (n+1) \, z_n^2.$$

The first inequality is log-convexity; for positive terms the second is log-concavity of
$z_n / n!$ with denominators cleared, the factorial using the original index $n$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 3. -/
public theorem motzkinNumber_add_motzkinAlternatingSum_logBalanced (n : ℕ) (hn : 7 ≤ n) :
    ((motzkinNumber n : ℤ) + motzkinAlternatingSum n) ^ 2 ≤
        ((motzkinNumber (n - 1) : ℤ) + motzkinAlternatingSum (n - 1)) *
          ((motzkinNumber (n + 1) : ℤ) + motzkinAlternatingSum (n + 1)) ∧
      n * (((motzkinNumber (n - 1) : ℤ) + motzkinAlternatingSum (n - 1)) *
          ((motzkinNumber (n + 1) : ℤ) + motzkinAlternatingSum (n + 1))) ≤
        (n + 1) * ((motzkinNumber n : ℤ) + motzkinAlternatingSum n) ^ 2 := by
  by_cases hn' : 9 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simpa [Nat.cast_add, add_assoc] using
      motzkinNumber_add_motzkinAlternatingSum_logBalanced.sum_tail k (by omega)
  · interval_cases n <;>
      simp only [motzkinAlternatingSum, motzkinNumber_eq_sum_range_half,
        catalan_eq_centralBinom_div] <;> decide

end

end MetaMathlibExt
