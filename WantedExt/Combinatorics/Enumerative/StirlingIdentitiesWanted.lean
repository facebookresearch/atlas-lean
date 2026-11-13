/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Some new identities for Stirling numbers

Statements from Kwankyu Lee, "Some New Identities for Stirling Numbers",
*Journal of Integer Sequences* 29 (2026), Article 26.2.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Lee/lee14.html>).

The paper's Stirling numbers of the first kind are unsigned, so they are
Mathlib's `Nat.stirlingFirst`; its second kind is `Nat.stirlingSecond`.
All identities are stated over `ℤ`. The four identities with the factor
`1 / (n - k)` are written after clearing that denominator. In Theorem 8,
the generalized binomial coefficient is expanded by
`binom{-k}{j} = (-1)^j * binom{k + j - 1}{j}`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

/-- **Lee's expansion of shifted Stirling numbers of the first kind.** Write $c(n, k)$ for the
unsigned Stirling number of the first kind, the number of permutations of $n$ elements with
exactly $k$ cycles. For natural numbers $m \le n$, the following identity of integers holds:
$$c(n + 1, m + 1) = \sum_{k=m}^{n} (-1)^{n-k} \binom{k}{m}\, n^{k-m}\, c(n, k).$$

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 1
(TeX label `thm:cksdd`). -/
theorem_wanted stirlingFirst_succ_eq_sum_choose_pow {m n : ℕ} (hmn : m ≤ n) :
    (Nat.stirlingFirst (n + 1) (m + 1) : ℤ) =
      ∑ k ∈ Finset.Icc m n,
        (Nat.stirlingFirst n k : ℤ) * (Nat.choose k m : ℤ) *
          (-1 : ℤ) ^ (n - k) * (n : ℤ) ^ (k - m)

/-- **Lee's alternating expansion of Stirling numbers of the second kind.** Write $S(n, k)$ for
the Stirling number of the second kind, the number of partitions of an $n$-element set into $k$
nonempty blocks. For natural numbers $m \le n$, the following identity of integers holds:
$$S(n, m) = \sum_{k=m}^{n} (-1)^{k-m} \binom{n}{k}\, m^{n-k}\, S(k, m).$$

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 2
(TeX label `thm:kscasc`). -/
theorem_wanted stirlingSecond_eq_sum_choose_pow {m n : ℕ} (hmn : m ≤ n) :
    (Nat.stirlingSecond n m : ℤ) =
      ∑ k ∈ Finset.Icc m n,
        (Nat.choose n k : ℤ) * (Nat.stirlingSecond k m : ℤ) *
          (m : ℤ) ^ (n - k) * (-1 : ℤ) ^ (k - m)

/-- **Lee's identity for Stirling numbers of the second kind from smaller rows.** Write $S(n, k)$
for the Stirling number of the second kind, the number of partitions of an $n$-element set into
$k$ nonempty blocks. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$, the
following identity of integers holds:
$$(n - k)\, S(n, k) = \sum_{j=2}^{n-k+1} (-1)^j \binom{n}{j}\, S(n-j+1, k).$$

This is Lee's Theorem 4 with the denominator $n - k$ cleared.

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 4
(TeX label `thm:mxcnd`). -/
theorem_wanted stirlingSecond_mul_sub_eq_sum_choose_alternating
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ((n : ℤ) - k) * (Nat.stirlingSecond n k : ℤ) =
      ∑ j ∈ Finset.Icc 2 (n - k + 1),
        (Nat.choose n j : ℤ) * (Nat.stirlingSecond (n - j + 1) k : ℤ) *
          (-1 : ℤ) ^ j

/-- **Lee's factorial-weighted alternating row sum of Stirling numbers of the second kind.** Write
$S(a, j)$ for the Stirling number of the second kind, the number of partitions of an $a$-element
set into $j$ nonempty blocks. For every natural number $a \ge 1$, the following identity of
integers holds:
$$\sum_{j=2}^{a} (-1)^j\, (j-2)!\, S(a, j) = a - 1.$$

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Lemma 6
(TeX label `lem:mjkfwd`). -/
theorem_wanted sum_stirlingSecond_factorial_alternating
    {a : ℕ} (ha : 1 ≤ a) :
    (∑ j ∈ Finset.Icc 2 a,
      (Nat.stirlingSecond a j : ℤ) * (Nat.factorial (j - 2) : ℤ) *
        (-1 : ℤ) ^ j) = (a : ℤ) - 1

/-- **Lee's identity for Stirling numbers of the second kind from higher columns.** Write
$S(n, k)$ for the Stirling number of the second kind, the number of partitions of an $n$-element
set into $k$ nonempty blocks. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$,
the following identity of integers holds:
$$(n - k)\, S(n, k) = \sum_{j=2}^{n-k+1} (j-2)!\, (-1)^j \binom{k+j-1}{j}\, S(n, k+j-1).$$

This is Lee's Theorem 8 with the denominator $n - k$ cleared and the generalized binomial
coefficient written as $\binom{-k}{j} = (-1)^j \binom{k+j-1}{j}$.

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 8
(TeX label `thm:dwdwf`). -/
theorem_wanted stirlingSecond_mul_sub_eq_sum_factorial_negChoose
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ((n : ℤ) - k) * (Nat.stirlingSecond n k : ℤ) =
      ∑ j ∈ Finset.Icc 2 (n - k + 1),
        (Nat.factorial (j - 2) : ℤ) *
          ((-1 : ℤ) ^ j * (Nat.choose (k + j - 1) j : ℤ)) *
          (Nat.stirlingSecond n (k + j - 1) : ℤ)

/-- **Lee's identity for Stirling numbers of the first kind from smaller rows.** Write $c(n, k)$
for the unsigned Stirling number of the first kind, the number of permutations of $n$ elements
with exactly $k$ cycles. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$, the
following identity of integers holds:
$$(n - k)\, c(n, k) = \sum_{j=2}^{n-k+1} \binom{n}{j}\, (j-2)!\, c(n-j+1, k).$$

This is Lee's Theorem 11 with the denominator $n - k$ cleared.

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 11
(TeX label `thm:mdkda`). -/
theorem_wanted stirlingFirst_mul_sub_eq_sum_choose_factorial
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ((n : ℤ) - k) * (Nat.stirlingFirst n k : ℤ) =
      ∑ j ∈ Finset.Icc 2 (n - k + 1),
        (Nat.choose n j : ℤ) * (Nat.stirlingFirst (n - j + 1) k : ℤ) *
          (Nat.factorial (j - 2) : ℤ)

/-- **Lee's identity for Stirling numbers of the first kind from higher columns.** Write $c(n, k)$
for the unsigned Stirling number of the first kind, the number of permutations of $n$ elements
with exactly $k$ cycles. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$, the
following identity of integers holds:
$$(n - k)\, c(n, k) = \sum_{j=2}^{n-k+1} \binom{k+j-1}{j}\, c(n, k+j-1).$$

This is Lee's Theorem 14 with the denominator $n - k$ cleared.

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 14
(TeX label `thm:dwfmc`). -/
theorem_wanted stirlingFirst_mul_sub_eq_sum_stirlingFirst_choose
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ((n : ℤ) - k) * (Nat.stirlingFirst n k : ℤ) =
      ∑ j ∈ Finset.Icc 2 (n - k + 1),
        (Nat.stirlingFirst n (k + j - 1) : ℤ) *
          (Nat.choose (k + j - 1) j : ℤ)

end MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted
