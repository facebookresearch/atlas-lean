/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.IncompleteLeonardoP
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination

/-!
# Binomial sum identity for incomplete Leonardo p-numbers

The identity follows by induction on `r`: Pascal's rule for the coefficients `(r + 1).choose i`
splits the sum for `r + 1` into the sums for `r` at `(n, k)` and at `(n + p, k + 1)`, and one
application of the recurrence `incompleteLeonardoP_succ` joins their right-hand sides.
-/

namespace MetaMathlibExt

public section

/-- **Binomial sum identity for incomplete Leonardo p-numbers.** For natural numbers $p \ge 1$,
$n$, $r$ and $k$ with $n \ge p + r$ and $k \le \lfloor (n - p - r)/(p + 1) \rfloor$, the
incomplete Leonardo $p$-numbers $\mathcal{L}_{p,m}(j)$ satisfy
$$
\sum_{i=0}^{r} \binom{r}{i} \mathcal{L}_{p,n+pi}(k + i) + (2^r - 1) p =
\mathcal{L}_{p,n+(p+1)r}(k + r).
$$

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 7. -/
theorem sum_choose_mul_incompleteLeonardoP (p n r k : ℕ) (hp : 1 ≤ p)
    (hnr : p + r ≤ n) (hk : k ≤ (n - p - r) / (p + 1)) :
    ∑ i ∈ Finset.range (r + 1), (r.choose i : ℤ) * incompleteLeonardoP p (n + p * i) (k + i) +
        ((2 : ℤ) ^ r - 1) * p =
      incompleteLeonardoP p (n + (p + 1) * r) (k + r) := by
  induction r generalizing n k with
  | zero => simp
  | succ r ih =>
    -- The bound on `k` without division, for `omega`.
    have hk' : k * (p + 1) ≤ n - p - (r + 1) := (Nat.le_div_iff_mul_le (by omega)).1 hk
    -- The identity for `r` at `(n, k)` and at `(n + p, k + 1)`.
    have h₁ := ih n k (by omega) (hk.trans (Nat.div_le_div_right (by omega)))
    have h₂ := ih (n + p) (k + 1) (by omega)
      ((Nat.le_div_iff_mul_le (by omega)).2 (by rw [add_mul, one_mul]; omega))
    -- The recurrence at index `n + (p + 1) * (r + 1)` and order `k + r + 1`.
    have h₃ : incompleteLeonardoP p (n + (p + 1) * (r + 1)) (k + (r + 1)) =
        incompleteLeonardoP p (n + p + (p + 1) * r) (k + 1 + r) +
          incompleteLeonardoP p (n + (p + 1) * r) (k + r) + p := by
      have h := incompleteLeonardoP_succ p (n + p + (p + 1) * r + 1) (k + r) hp (by omega)
        ((Nat.le_div_iff_mul_le (by omega)).2 (by rw [add_mul, mul_comm r]; omega))
      rw [show n + p + (p + 1) * r + 1 - 1 = n + p + (p + 1) * r by omega,
        show n + p + (p + 1) * r + 1 - p - 1 = n + (p + 1) * r by omega] at h
      rw [show n + (p + 1) * (r + 1) = n + p + (p + 1) * r + 1 by ring,
        show k + (r + 1) = k + r + 1 by omega, show k + 1 + r = k + r + 1 by omega]
      exact h
    -- Pascal's rule splits the sum for `r + 1` into the sums of `h₁` and `h₂`.
    rw [Finset.sum_choose_succ_mul (fun i _ => incompleteLeonardoP p (n + p * i) (k + i)) r]
    have e : ∀ i ∈ Finset.range (r + 1),
        (r.choose i : ℤ) * incompleteLeonardoP p (n + p * (i + 1)) (k + (i + 1)) =
          (r.choose i : ℤ) * incompleteLeonardoP p (n + p + p * i) (k + 1 + i) := by
      intro i _
      rw [show n + p * (i + 1) = n + p + p * i by ring, show k + (i + 1) = k + 1 + i by omega]
    rw [Finset.sum_congr rfl e]
    linear_combination h₁ + h₂ - h₃

end

end MetaMathlibExt
