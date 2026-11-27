/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Incomplete Leonardo p-numbers

Pascal's identity splits the defining binomial sum into the two shorter sums in the recurrence.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Incomplete Leonardo p-numbers.** For natural numbers $p$, $n$ and $k$, the incomplete
Leonardo $p$-number is the integer
$$
\mathcal{L}_{p,n}(k) = (p + 1) \sum_{i=0}^{k} \binom{\max(n - pi, 0)}{i} - p.
$$
On the paper's range $0 \le k \le \lfloor n/(p+1) \rfloor$ the maximum is always $n - pi$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, display (4). -/
def incompleteLeonardoP (p n k : ℕ) : ℤ :=
  (p + 1) * ∑ i ∈ Finset.range (k + 1), ((n - p * i).choose i : ℤ) - p

/-- **Incomplete Leonardo p-numbers at zero.** For all natural numbers $p$ and $n$, the
incomplete Leonardo $p$-number $\mathcal{L}_{p,n}(0)$ equals $1$.

Source: Belkhir and Tan, INTEGERS 25 (2025), Article A57, display (4). -/
theorem incompleteLeonardoP_zero (p n : ℕ) : incompleteLeonardoP p n 0 = 1 := by
  simp [incompleteLeonardoP]

-- The binomial identity works for every cutoff and also for p = 0.
set_option linter.unusedVariables false in
/-- **Recurrence for incomplete Leonardo p-numbers.** For natural numbers $p \ge 1$, $n > p$ and
$k \le \lfloor n/(p+1) \rfloor$, the incomplete Leonardo $p$-numbers $\mathcal{L}_{p,m}(j)$
satisfy
$$
\mathcal{L}_{p,n}(k + 1) = \mathcal{L}_{p,n-1}(k + 1) + \mathcal{L}_{p,n-p-1}(k) + p.
$$

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 6. -/
theorem incompleteLeonardoP_succ (p n k : ℕ) (hp : 1 ≤ p) (hn : p < n)
    (hk : k ≤ n / (p + 1)) :
    incompleteLeonardoP p n (k + 1) =
      incompleteLeonardoP p (n - 1) (k + 1) + incompleteLeonardoP p (n - p - 1) k + p := by
  have pascal (i : ℕ) :
      (n - p * (i + 1)).choose (i + 1) =
        (n - p - 1 - p * i).choose i + (n - 1 - p * (i + 1)).choose (i + 1) := by
    rw [Nat.mul_succ]
    have h₁ : n - p - 1 - p * i = n - (p * i + p) - 1 := by omega
    have h₂ : n - 1 - (p * i + p) = n - (p * i + p) - 1 := by omega
    rw [h₁, h₂]
    by_cases h : 0 < n - (p * i + p)
    · exact Nat.choose_succ_right _ _ h
    · have hi : i ≠ 0 := by
        rintro rfl
        exact h (by simpa using Nat.sub_pos_of_lt hn)
      rw [show n - (p * i + p) = 0 by omega]
      simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hi)]
  unfold incompleteLeonardoP
  rw [Finset.sum_range_succ' _ (k + 1),
    Finset.sum_range_succ' (fun i => ((n - 1 - p * i).choose i : ℤ)) (k + 1)]
  simp only [pascal, Nat.cast_add, Finset.sum_add_distrib, Nat.choose_zero_right, mul_add]
  omega

end

end MetaMathlibExt
