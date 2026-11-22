/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `2`-intersecting families of `2n`-subsets of `[4n]` (Erdős Problem 83)

Erdős Problem 83 (Erdős, Ko and Rado): if `F` is a family of subsets of `[4n]` with `|A| = 2n` for
all `A ∈ F` and `|A ∩ B| ≥ 2` for all `A, B ∈ F`, then `|F| ≤ (C(4n, 2n) - C(2n, n)²) / 2`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.TwoIntersectingHalfSetsErdosProblem83Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #83, https://www.erdosproblems.com/83 (status PROVED
(LEAN)). UnsolvedMath record UM-30006715 (`EP-83`), dataset ulamai/UnsolvedMath v1.8.0.

The bound is stated without division or truncated subtraction as `2 |F| + C(2n, n)² ≤ C(4n, 2n)`
(`C(4n, 2n) - C(2n, n)²` is even). It is attained by the `2n`-sets with at least `n + 1` elements in
`[2n]`. Compared with the formal-conjectures statement `ErdosProblems/83.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 83 (Erdős, Ko and Rado): a family of `2n`-element subsets of a `4n`-element set in
which any two members share at least two elements has at most
`(C(4n, 2n) - C(2n, n)²) / 2` members. -/
def twoIntersectingHalfSetsBound : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))), (∀ A ∈ F, A.card = 2 * n) →
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) →
      2 * F.card + (2 * n).choose n ^ 2 ≤ (4 * n).choose (2 * n)

/--
Resolved true: Ahlswede and Khachatrian proved the conjecture as a case of their complete
intersection theorem, which determines the largest `t`-intersecting families of `k`-subsets of
`[m]`; the bound is attained by the `2n`-sets with at least `n + 1` elements of `[2n]`.
erdosproblems.com/83 lists the problem as proved (Lean). Source: T. F. Bloom, Erdős Problems,
Problem #83, https://www.erdosproblems.com/83 (status PROVED (LEAN)); resolution: R. Ahlswede and L.
H. Khachatrian, The complete intersection theorem for systems of finite sets, European J. Combin. 18
(1997), 125-136, erdosproblems.com/83: for 2 ≤ t ≤ k ≤ m and r with 1/(r + 1) ≤ (m - 2k + 2t -
2)/((t - 1)(k - t + 1)) < 1/r, the largest family of k-subsets of [m] with pairwise intersections of
size at least t consists of the k-sets with at least t + r elements of {1, …, t + 2r}; for m = 4n, k
= 2n, t = 2 the ratio is 2/(2n - 1), so r = n - 1 and the family is the 2n-sets with at least n + 1
elements of [2n], https://doi.org/10.1006/eujc.1995.0092.
-/
public theorem_wanted twoIntersectingHalfSetsBound_holds : twoIntersectingHalfSetsBound

end MathlibExt.Combinatorics.TwoIntersectingHalfSetsErdosProblem83Wanted
