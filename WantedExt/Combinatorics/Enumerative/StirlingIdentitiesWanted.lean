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
All identities are stated over `ℤ`. The identities with the factor
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
public import MathlibExt.Combinatorics.Enumerative.StirlingFirstHigherColumns
public import MathlibExt.Combinatorics.Enumerative.StirlingFirstShiftedExpansion
public import MathlibExt.Combinatorics.Enumerative.StirlingFirstSmallerRows
public import MathlibExt.Combinatorics.Enumerative.StirlingSecondAlternatingRowSum
public import MathlibExt.Combinatorics.Enumerative.StirlingSecondSignedBinomialTransform
public import MathlibExt.Combinatorics.Enumerative.StirlingSecondSmallerRows

set_option autoImplicit false

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

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

end MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted
