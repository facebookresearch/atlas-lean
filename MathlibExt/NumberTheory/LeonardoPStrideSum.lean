/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LeonardoP

/-!
# Stride sums of generalized Leonardo `p`-numbers

The recurrence turns the sum at stride `p + 1` into a telescoping sum. The
endpoint correction is determined by whether `m + 1` lies in the initial block.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.LeonardoPWanted

-- The statement retains both positivity hypotheses from the source.
set_option linter.unusedVariables false in
/-- **Stride sums of the generalized Leonardo $p$-numbers.** Let $p \ge 1$ and $k \ge 1$ be
natural numbers, and let $\mathcal{L}_{p,k}$ denote the generalized Leonardo $p$-numbers
($\mathcal{L}_{p,k}(j) = 1$ for $0 \le j \le p$ and
$\mathcal{L}_{p,k}(j) = \mathcal{L}_{p,k}(j-1) + \mathcal{L}_{p,k}(j-p-1) + k$ for $j > p$).
Then for all natural numbers $m \le p$ and $n$, the sum
$S = \sum_{i=0}^{n} \mathcal{L}_{p,k}((p+1)i + m)$ satisfies
$S = \mathcal{L}_{p,k}((p+1)n + m + 1) - kn$ if $m < p$, and
$S = \mathcal{L}_{p,k}((p+1)(n+1)) - k(n+1) - 1$ if $m = p$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 4. -/
theorem sum_leonardoPK_stride (p k m n : ℕ)
    (hp : 1 ≤ p) (hk : 1 ≤ k) (hm : m ≤ p) :
    ∑ i ∈ Finset.range (n + 1), leonardoPK p k ((p + 1) * i + m) =
      if m < p then
        leonardoPK p k ((p + 1) * n + m + 1) - (k : ℤ) * n
      else
        leonardoPK p k ((p + 1) * (n + 1)) - (k : ℤ) * (n + 1) - 1 := by
  let stride (i : ℕ) := (p + 1) * i + m
  have diff (i : ℕ) :
      leonardoPK p k (stride (i + 1) + 1) - leonardoPK p k (stride i + 1) =
        leonardoPK p k (stride (i + 1)) + k := by
    have hstep : p + (stride i + 1) = stride (i + 1) := by
      simp only [stride, Nat.mul_succ]
      omega
    have hrec := leonardoPK_recurrence p k (stride i + 1)
    rw [hstep] at hrec
    omega
  have hsum : (∑ i ∈ Finset.range (n + 1), leonardoPK p k (stride i)) =
      leonardoPK p k (stride n + 1) - (k : ℤ) * n - leonardoPK p k (m + 1) + 1 := by
    have h := Finset.sum_range_sub (fun i => leonardoPK p k (stride i + 1)) n
    simp only [diff, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_comm (n : ℤ) (k : ℤ)] at h
    rw [Finset.sum_range_succ']
    simp only [show stride 0 = m by simp [stride], leonardoPK_of_le p k m hm] at h ⊢
    omega
  rw [hsum]
  dsimp only [stride]
  by_cases hmp : m < p
  · rw [ite_eq_left hmp, leonardoPK_of_le p k (m + 1) hmp, sub_add_cancel]
  · have heq : m = p := Nat.le_antisymm hm (Nat.le_of_not_gt hmp)
    subst m
    have hend : (p + 1) * n + p + 1 = (p + 1) * (n + 1) := by
      rw [Nat.mul_succ]
      omega
    have hfirst : leonardoPK p k (p + 1) = 1 + 1 + (k : ℤ) := by
      simpa only [Nat.add_zero, leonardoPK_of_le p k p le_rfl,
        leonardoPK_of_le p k 0 (Nat.zero_le p)] using leonardoPK_recurrence p k 0
    rw [ite_eq_right (Nat.lt_irrefl p), hend, hfirst]
    simp only [mul_add, mul_one]
    omega

end MathlibExt.NumberTheory.LeonardoPWanted
