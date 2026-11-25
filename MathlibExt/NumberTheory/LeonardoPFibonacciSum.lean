/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LeonardoP
public import MathlibExt.NumberTheory.Recurrences.HonsbergerFibonacciP

/-!
# Sums of consecutive Fibonacci `p`-numbers

The sum of `p + 1` consecutive Fibonacci `p`-numbers, scaled by `k + 1`, gives a shifted
generalized Leonardo `p`-number plus `k`.
-/

public section

namespace MathlibExt.NumberTheory.LeonardoPWanted

open MetaMathlibExt

private theorem fibonacciP_step (p i : ℕ) :
    (fibonacciP p (p + i + 1) : ℤ) = (fibonacciP p (p + i) : ℤ) + fibonacciP p i := by
  rw [fibonacciP, ite_eq_right (by omega), Nat.add_sub_cancel_left, Nat.cast_add]

-- Adding k makes the Leonardo recurrence homogeneous, with initial terms scaled by k + 1.
private theorem scaled_fibonacciP (p k : ℕ) (hp : 1 ≤ p) (m : ℕ) :
    ((k : ℤ) + 1) * (fibonacciP p (m + 1) : ℤ) = leonardoPK p k m + k := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m ≤ p
    · have h : fibonacciP p (m + 1) = 1 := by
        rcases hm.lt_or_eq with hlt | heq
        · exact fibonacciP_eq_one p _ (by omega) hlt
        · subst m
          rw [fibonacciP, ite_eq_right (by omega), Nat.sub_self, fibonacciP_zero, Nat.add_zero,
            fibonacciP_eq_one p p hp le_rfl]
      simp [h, leonardoPK_of_le p k m hm, add_comm]
    · obtain ⟨i, rfl⟩ : ∃ i, m = p + i + 1 := ⟨m - p - 1, by omega⟩
      rw [leonardoPK_recurrence, show p + i + 1 + 1 = p + (i + 1) + 1 by omega,
        fibonacciP_step, ← Nat.add_assoc, mul_add, ih (p + i) (by omega), ih i (by omega)]
      omega

/-- **Sums of $p+1$ consecutive Fibonacci $p$-numbers.** Let $p \ge 1$ and $n \ge 1$ be natural
numbers and let $k$ be a natural number. Let $F_p$ denote the Fibonacci $p$-numbers
($F_p(0) = 0$, $F_p(m) = 1$ for $1 \le m \le p$, and $F_p(m) = F_p(m-1) + F_p(m-p-1)$ for
$m > p$), and let $\mathcal{L}_{p,k}$ denote the generalized Leonardo $p$-numbers
($\mathcal{L}_{p,k}(m) = 1$ for $0 \le m \le p$ and
$\mathcal{L}_{p,k}(m) = \mathcal{L}_{p,k}(m-1) + \mathcal{L}_{p,k}(m-p-1) + k$ for $m > p$).
Then $(k+1) \sum_{i=0}^{p} F_p(n+i) = \mathcal{L}_{p,k}(n+2p-1) + k$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Lemma 12. -/
theorem succ_mul_sum_fibonacciP (p k n : ℕ) (hp : 1 ≤ p)
    (hn : 1 ≤ n) :
    ((k : ℤ) + 1) * ∑ i ∈ Finset.range (p + 1), (MetaMathlibExt.fibonacciP p (n + i) : ℤ) =
      leonardoPK p k (n + 2 * p - 1) + (k : ℤ) := by
  let f (i : ℕ) : ℤ := fibonacciP p (p + (n + i))
  have diff (i : ℕ) : f (i + 1) - f i = fibonacciP p (n + i) := by
    simp only [f, ← Nat.add_assoc n i 1, ← Nat.add_assoc p (n + i) 1, fibonacciP_step]
    omega
  have h := Finset.sum_range_sub f p
  simp only [diff] at h
  rw [Finset.sum_range_succ, h, show f 0 = fibonacciP p (n + p) by simp [f, Nat.add_comm]]
  rw [sub_add_cancel, ← scaled_fibonacciP p k hp, show n + 2 * p - 1 + 1 = p + (n + p) by omega]

end MathlibExt.NumberTheory.LeonardoPWanted
