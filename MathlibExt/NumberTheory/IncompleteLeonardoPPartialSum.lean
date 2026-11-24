/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.IncompleteLeonardoP

/-!
# Partial sums of incomplete Leonardo p-numbers

The recurrence expresses each summand plus `p` as the difference of consecutive terms
at order `k + 1`. Summing these differences leaves the two endpoints.
-/

namespace MetaMathlibExt

/-- **Partial sums of incomplete Leonardo p-numbers.** For natural numbers $p \ge 1$, $n$, $k$ and
$r$ with $n \ge (p + 1)(k + 1)$, the incomplete Leonardo $p$-numbers $\mathcal{L}_{p,m}(j)$
satisfy
$$
\sum_{i=0}^{r-1} \mathcal{L}_{p,n-p+i}(k) + rp =
\mathcal{L}_{p,n+r}(k + 1) - \mathcal{L}_{p,n}(k + 1),
$$
where the sum is empty when $r = 0$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 8. -/
public theorem sum_incompleteLeonardoP (p n k r : ℕ) (hp : 1 ≤ p)
    (hn : (p + 1) * (k + 1) ≤ n) :
    ∑ i ∈ Finset.range r, incompleteLeonardoP p (n - p + i) k + (r : ℤ) * p =
      incompleteLeonardoP p (n + r) (k + 1) - incompleteLeonardoP p n (k + 1) := by
  rw [Nat.mul_succ] at hn
  induction r with
  | zero => simp
  | succ r ih =>
    have hk : k ≤ (n + r + 1) / (p + 1) := by
      apply (Nat.le_div_iff_mul_le (by omega)).2
      rw [Nat.mul_comm k]
      omega
    have step := incompleteLeonardoP_succ p (n + r + 1) k hp (by omega) hk
    rw [Nat.add_sub_cancel, show n + r + 1 - p - 1 = n - p + r by omega] at step
    rw [Finset.sum_range_succ, Nat.cast_succ, add_mul, one_mul, Nat.add_succ n r, step]
    omega

end MetaMathlibExt
