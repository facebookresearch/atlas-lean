/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.JosephusFunction
public import MathlibExt.Combinatorics.MaximumNimJosephus
import Mathlib.Logic.Function.Iterate

/-!
# The shifted Maximum Nim iteration for Josephus survivors

The first iterate to reach `n * (k - 1)` is `n * k - josephus k n`. To advance from `n` to
`n + 1`, Euler's recurrence gives the number of further steps as the quotient of
`josephus k n + k - 1` by `n + 1`. Until the new threshold is reached, each of those steps adds
`n + 1`. The quotient can be zero, in which case the two thresholds share a first crossing.
-/

namespace MetaMathlibExt

/-- The first iterate reaching the threshold for a nonempty circle, including iteration zero
for a singleton. The invariant is stated additively to avoid truncated subtraction. -/
private theorem josephus_first_crossing (k n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
    ∃ p, Nat.iterate (maximumNimH k) p (k - 1) + josephus k n = n * k ∧
      ∀ q < p, Nat.iterate (maximumNimH k) q (k - 1) < n * (k - 1) := by
  let a (p : ℕ) := Nat.iterate (maximumNimH k) p (k - 1)
  change ∃ p, a p + josephus k n = n * k ∧ ∀ q < p, a q < n * (k - 1)
  have hk' : 0 < k - 1 := by omega
  have hthreshold (m : ℕ) : m * (k - 1) + m = m * k := by
    rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by omega))]
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨0, ?_, fun q hq => (Nat.not_lt_zero q hq).elim⟩
    simpa only [a, Function.iterate_zero_apply, josephus_one k hk, Nat.one_mul] using
      hthreshold 1
  | succ n hn ih =>
    obtain ⟨p, hp, hfirst⟩ := ih
    let s := (josephus k n + k - 1) / (n + 1)
    have hdiv : (josephus k n + k - 1) % (n + 1) + s * (n + 1) = josephus k n + k - 1 := by
      simpa only [s, Nat.mul_comm] using Nat.mod_add_div (josephus k n + k - 1) (n + 1)
    have hnext : a p + s * (n + 1) + josephus k (n + 1) = (n + 1) * k := by
      rw [josephus_succ k n hk hn, Nat.succ_mul]
      omega
    have hlow : n * (k - 1) ≤ a p := by
      have hJ := (josephus_range k n hk hn).2
      have ht := hthreshold n
      omega
    have hhigh : a p + s * (n + 1) < (n + 1) * k := by
      have hJ := (josephus_range k (n + 1) hk (by omega)).1
      omega
    have hbefore (j : ℕ) (hj : j < s) : a p + j * (n + 1) < (n + 1) * (k - 1) := by
      have hle := Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt hj)
      rw [Nat.succ_mul] at hle
      have ht := hthreshold (n + 1)
      omega
    -- Before the crossing, the quotient in `maximumNimH` stays equal to `n`.
    have hiter (j : ℕ) (hj : j ≤ s) : a (p + j) = a p + j * (n + 1) := by
      induction j with
      | zero => simp
      | succ j ih =>
        have hj' : j < s := by omega
        have hlo : n * (k - 1) ≤ a p + j * (n + 1) := hlow.trans (Nat.le_add_right _ _)
        have hquot : (a p + j * (n + 1)) / (k - 1) = n :=
          Nat.le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hk').2 (hbefore j hj')))
            ((Nat.le_div_iff_mul_le hk').2 hlo)
        rw [show a (p + (j + 1)) = maximumNimH k (a (p + j)) from
          Function.iterate_succ_apply' _ _ _, ih hj'.le, maximumNimH, hquot, Nat.succ_mul]
        omega
    refine ⟨p + s, (congrArg (· + josephus k (n + 1)) (hiter s le_rfl)).trans hnext, ?_⟩
    intro q hq
    rcases lt_or_ge q p with hqp | hpq
    · exact (hfirst q hqp).trans_le (Nat.mul_le_mul_right (k - 1) (Nat.le_succ n))
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hpq
      have hj : j < s := by omega
      rw [hiter j hj.le]
      exact hbefore j hj

/-- **Josephus survivor via the shifted iteration.** Let $k \ge 2$ and $n \ge 2$ be natural
numbers, let $h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ for natural numbers $x$, and write
$h_k^p$ for the $p$-th iterate of $h_k$. Then there is a natural number $p \ge 1$ with
$h_k^{p-1}(k-1) < n(k-1) \le h_k^p(k-1)$ and $J_k(n) = nk - h_k^p(k-1)$, where $J_k$ is the
Josephus function for elimination step $k$.

The hypothesis $n \ge 2$ is needed: for $n = 1$ every $p \ge 1$ has
$h_k^{p-1}(k-1) \ge k - 1 = n(k-1)$, so no such $p$ exists.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Corollary 1 (`integers-2024-G5-cor-1`). -/
public theorem josephus_eq_mul_sub_iterate_maximumNimH_pred (k n : ℕ)
    (hk : 2 ≤ k) (hn : 2 ≤ n) :
    ∃ p, 1 ≤ p ∧
      Nat.iterate (maximumNimH k) (p - 1) (k - 1) < n * (k - 1) ∧
      n * (k - 1) ≤ Nat.iterate (maximumNimH k) p (k - 1) ∧
      josephus k n = n * k - Nat.iterate (maximumNimH k) p (k - 1) := by
  obtain ⟨p, hp, hfirst⟩ := josephus_first_crossing k n hk (by omega)
  have hJ := (josephus_range k n hk (by omega)).2
  have hthreshold : n * (k - 1) + n = n * k := by
    rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by omega))]
  have hreach : n * (k - 1) ≤ Nat.iterate (maximumNimH k) p (k - 1) := by omega
  have hpos : 1 ≤ p := by
    by_contra h
    have hp0 : p = 0 := by omega
    rw [hp0, Function.iterate_zero_apply] at hreach
    have hmul := Nat.mul_le_mul_right (k - 1) hn
    rw [show 2 * (k - 1) = (k - 1) + (k - 1) from Nat.two_mul _] at hmul
    omega
  exact ⟨p, hpos, hfirst (p - 1) (by omega), hreach, by omega⟩

end MetaMathlibExt
