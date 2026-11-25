/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.List.GetD

/-!
# Partial sums of the generalized Leonardo `p`-numbers

The recurrence expresses each summand plus `k` as a difference of consecutive shifted terms.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.LeonardoPWanted

/-- **Initial values of the generalized Leonardo $p$-numbers.** For natural numbers $p$, $k$
and $n$, this is the list of integers $(\mathcal{L}_{p,k}(0), \mathcal{L}_{p,k}(1), \dots,
\mathcal{L}_{p,k}(n))$ of length $n + 1$, where $\mathcal{L}_{p,k}(i) = 1$ for $0 \le i \le p$
and $\mathcal{L}_{p,k}(i) = \mathcal{L}_{p,k}(i-1) + \mathcal{L}_{p,k}(i-p-1) + k$ for $i > p$. -/
def leonardoPKSeq (p k : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
      let prev := leonardoPKSeq p k n
      prev ++ [if n + 1 ≤ p then 1
        else prev.getD n 0 + prev.getD (n - p) 0 + (k : ℤ)]

/-- **Generalized Leonardo $p$-numbers.** For natural numbers $p$ and $k$, the generalized
Leonardo $p$-numbers are the integers $\mathcal{L}_{p,k}(n)$, $n \in \mathbb{N}$, given by
$\mathcal{L}_{p,k}(n) = 1$ for $0 \le n \le p$ and
$\mathcal{L}_{p,k}(n) = \mathcal{L}_{p,k}(n-1) + \mathcal{L}_{p,k}(n-p-1) + k$ for $n > p$. -/
def leonardoPK (p k n : ℕ) : ℤ := (leonardoPKSeq p k n).getD n 0

/-- **Generalized Leonardo $p$-numbers at integer arguments.** For natural numbers $p$ and $k$
and an integer $z$, the value is the generalized Leonardo $p$-number $\mathcal{L}_{p,k}(z)$ if
$z \ge 0$, and $-k$ if $z < 0$.

For $-p \le z \le -1$ these are the values $\mathcal{L}_{p,k}(z) = -k$ obtained by running the
recurrence $\mathcal{L}_{p,k}(n) = \mathcal{L}_{p,k}(n-1) + \mathcal{L}_{p,k}(n-p-1) + k$
backwards; below $-p$ they need not be, but Theorem 13 of the source only uses arguments
$z \ge -p$. -/
def leonardoPKZ (p k : ℕ) (z : ℤ) : ℤ :=
  if 0 ≤ z then leonardoPK p k z.toNat else -(k : ℤ)

private theorem length_leonardoPKSeq (p k n : ℕ) : (leonardoPKSeq p k n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leonardoPKSeq, ih]

private theorem getD_leonardoPKSeq (p k i n : ℕ) (hi : i ≤ n) :
    (leonardoPKSeq p k n).getD i 0 = leonardoPK p k i := by
  induction n, hi using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [leonardoPKSeq, List.getD_append _ _ _ _ (by
      simpa only [length_leonardoPKSeq] using Nat.lt_succ_of_le hn)]
    exact ih

private theorem leonardoPK_succ (p k n : ℕ) :
    leonardoPK p k (n + 1) = if n + 1 ≤ p then 1
      else leonardoPK p k n + leonardoPK p k (n - p) + k := by
  rw [leonardoPK, leonardoPKSeq, List.getD_append_right _ _ _ _ (by rw [length_leonardoPKSeq]),
    length_leonardoPKSeq, Nat.sub_self, List.getD_cons_zero,
    getD_leonardoPKSeq p k (n - p) n (Nat.sub_le ..)]
  rfl

/-- Each of the first `p + 1` generalized Leonardo numbers is one. -/
theorem leonardoPK_of_le (p k n : ℕ) (hn : n ≤ p) : leonardoPK p k n = 1 := by
  cases n with
  | zero => rfl
  | succ n => simp [leonardoPK_succ, hn]

/-- For natural numbers $p,k,i$, the generalized Leonardo numbers satisfy
$\mathcal L_{p,k}(p+i+1)=\mathcal L_{p,k}(p+i)+\mathcal L_{p,k}(i)+k$. -/
theorem leonardoPK_recurrence (p k i : ℕ) :
    leonardoPK p k (p + i + 1) = leonardoPK p k (p + i) + leonardoPK p k i + k := by
  rw [leonardoPK_succ, ite_eq_right (by omega), Nat.add_sub_cancel_left]

-- The statement retains both positivity hypotheses from the source.
set_option linter.unusedVariables false in
/-- **Partial sums of the generalized Leonardo $p$-numbers.** Let $p \ge 1$ and $k \ge 1$ be
natural numbers, and let $\mathcal{L}_{p,k}$ denote the generalized Leonardo $p$-numbers
($\mathcal{L}_{p,k}(j) = 1$ for $0 \le j \le p$ and
$\mathcal{L}_{p,k}(j) = \mathcal{L}_{p,k}(j-1) + \mathcal{L}_{p,k}(j-p-1) + k$ for $j > p$).
Then for every natural number $n$,
$\sum_{i=0}^{n} \mathcal{L}_{p,k}(i) = \mathcal{L}_{p,k}(n+p+1) - k(n+1) - 1$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 3. -/
theorem sum_leonardoPK (p k n : ℕ) (hp : 1 ≤ p)
    (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range (n + 1), leonardoPK p k i =
      leonardoPK p k (n + p + 1) - (k : ℤ) * (n + 1) - 1 := by
  have diff (i : ℕ) : leonardoPK p k (p + (i + 1)) - leonardoPK p k (p + i) =
      leonardoPK p k i + k := by
    rw [Nat.add_succ, leonardoPK_recurrence]
    omega
  have h := Finset.sum_range_sub (fun i => leonardoPK p k (p + i)) (n + 1)
  simp only [diff, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, Nat.add_zero, leonardoPK_of_le p k p le_rfl] at h
  rw [← Nat.add_assoc p n 1, Nat.add_comm p n, mul_comm] at h
  omega

end MathlibExt.NumberTheory.LeonardoPWanted
