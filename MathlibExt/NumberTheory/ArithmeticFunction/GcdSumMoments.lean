/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Group.ForwardDiff

/-!
# An alternating binomial sum for moments of the mean gcd-sum function
-/

namespace MetaMathlibExt

/-- **An alternating binomial sum vanishes.** Let $k$ and $m$ be natural numbers with $k \ge 2$
and $m \ge 2^k - 1$. Then, computed in the integers,
$$\sum_{r=0}^{\min(2^k,\, m+1)} (-1)^r \binom{2^k}{r} (m + 1 - r)^k = 0.$$
Since $m + 1 \ge 2^k$, the upper limit of the sum is $2^k$.

This sum is the exponent $\ell_m$ of the paper: the coefficient of $p^{-ms}$ in
$(1 - p^{-s})^{2^k} \sum_{a \ge 0} (a + 1)^k p^{-as}$, which is why it stops at $r = m + 1$. The
paper prints the sum up to $r = 2^k$ for every $m$; that sum vanishes for every $m$, being a
$2^k$-th difference of a polynomial of degree $k$, which contradicts the paper's own
$\ell_2 = 3^k - 4^k + \binom{2^k}{2}$: for $k = m = 2$ the truncated sum is $-1$. So with the
truncation the hypothesis $m \ge 2^k - 1$ is needed. The paper's hypothesis $k \ge 2$ is kept: for
$k = 0$ the term $r = m + 1$ contributes $0^0 = 1$ rather than the coefficient of a negative
index, so the truncated sum is no longer the coefficient read off from the paper's Euler product.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Theorem 5 (`integers-2026-A70-thm-5`). -/
public theorem alternating_choose_two_pow_mul_pow_eq_zero (k m : ℕ) (hk : 2 ≤ k)
    (hm : 2 ^ k - 1 ≤ m) :
    ∑ r ∈ Finset.range (min (2 ^ k) (m + 1) + 1),
      (-1 : ℤ) ^ r * ((2 ^ k).choose r : ℤ) * ((m : ℤ) + 1 - r) ^ k = 0 := by
  set n := 2 ^ k
  have hkn : k < n := k.lt_two_pow_self
  have h := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) hkn) ((m : ℤ) + 1 - n)
  rw [fwdDiff_iter_eq_sum_shift] at h
  rw [min_eq_left (by omega), ← Finset.sum_range_reflect]
  refine (Finset.sum_congr rfl fun r hr => ?_).trans h
  have hrn : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  simp only [Nat.add_sub_cancel, Nat.choose_symm hrn, Nat.cast_sub hrn, zsmul_eq_mul, nsmul_one]
  congr 2
  omega

end MetaMathlibExt
