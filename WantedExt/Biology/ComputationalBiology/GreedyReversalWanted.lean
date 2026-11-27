/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The greedy breakpoint algorithm for unsigned sorting by reversals

An unsigned permutation `π` of `1, …, n` is framed by `π_0 = 0` and `π_{n+1} = n + 1`. A reversal
`(i, j)` with `1 ≤ i < j ≤ n` reverses the block `π_i … π_j`. A breakpoint is an adjacent pair
`(π_t, π_{t+1})`, `0 ≤ t ≤ n`, whose values do not differ by one; `φ(π)` is the number of
breakpoints. A strip is a maximal run of positions without breakpoints; a strip is decreasing if its
values decrease, where a single element is a decreasing strip unless it is `π_0` or `π_{n+1}`.
`OPT(π)` is the least number of reversals that sort `π`.

The greedy algorithm repeatedly chooses a reversal removing the most breakpoints, resolving ties
among reversals that remove one breakpoint in favour of reversals that leave a decreasing strip
(Fig. 2).

**Theorem 1** (Kececioglu–Sankoff 1995). The greedy algorithm sorts every permutation `π` with
at most `φ(π)` reversals.

**Corollary 1** (Kececioglu–Sankoff 1995). Since a reversal removes at most two breakpoints,
`OPT(π) ≥ φ(π)/2`, so the greedy algorithm uses at most `2 OPT(π)` reversals.

A greedy run is any sequence of reversals in which each reversal is a greedy choice at a
permutation other than the identity; every choice the algorithm may make is covered. Theorem 1
is stated as: every greedy run has at most `φ(π)` reversals, and some greedy run reaches the
identity. The ratio of Corollary 1 follows from Theorem 1 and `ub_le_two_mul_udist`, so it is not
stated here. The `O(n²)` time and `O(n)` space bounds, and the paper's exact branch-and-bound
algorithm, are not stated.

Unsigned permutations, block reversals, the framed breakpoint count `φ` and the reversal distance
are the canonical `UValid`, `revBlock`, `ubreaks` and `udist` of
`CSLibExt.Bioinformatics.Rearrangement.SortingByReversals` (lists over `ℤ`, zero-based positions:
the block `π_i … π_j` is `revBlock π (i - 1) (j - 1)`), where `ubreaks_eq_zero_iff` shows that the
identity is the only unsigned permutation without breakpoints.

Sources: J. Kececioglu and D. Sankoff, "Exact and approximation algorithms for sorting by
reversals, with application to genome rearrangement", Algorithmica 13(1-2):180-210, 1995,
doi:10.1007/BF01188586, Theorem 1 and Corollary 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.Rearrangement.SortingByReversals

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.GreedyReversalWanted

open Cslib.Bioinformatics.Rearrangement.SortingByReversals

/-- The identity permutation `[1, …, n]`. -/
def identity (n : ℕ) : List ℤ :=
  (List.Icc 1 n).map Int.ofNat

/-- The framed list `[0, π_1, …, π_n, n + 1]`. -/
def framed (n : ℕ) (π : List ℤ) : List ℤ :=
  0 :: π ++ [Int.ofNat (n + 1)]

/-- A reversal of an unsigned permutation of `1, …, n`, in zero-based positions: `i < j < n`, so
the block has at least two elements (a one-element reversal changes nothing). -/
def IsReversal (n : ℕ) (r : ℕ × ℕ) : Prop :=
  r.1 < r.2 ∧ r.2 < n

/-- The number of breakpoints removed by the reversal `r` (negative if it creates more breakpoints
than it removes). -/
def removal (n : ℕ) (π : List ℤ) (r : ℕ × ℕ) : ℤ :=
  (ubreaks n π : ℤ) - ubreaks n (revBlock π r.1 r.2)

/-- `π` has a decreasing strip: some framed position `1 ≤ t ≤ n` is a strip of a single element
(breakpoints on both sides, `isGap = 1`), or has `π_{t+1} + 1 = π_t` (it lies in a decreasing
strip of length at least two). -/
def HasDecreasingStrip (n : ℕ) (π : List ℤ) : Prop :=
  ∃ t, 1 ≤ t ∧ t ≤ n ∧
    ((isGap ((framed n π).getD (t - 1) 0) ((framed n π).getD t 0) = 1 ∧
        isGap ((framed n π).getD t 0) ((framed n π).getD (t + 1) 0) = 1) ∨
      (framed n π).getD (t + 1) 0 + 1 = (framed n π).getD t 0)

/-- `r` is a greedy choice at `π` (Kececioglu–Sankoff, Fig. 2): a reversal removing the most
breakpoints among all reversals, resolving ties among reversals that remove one breakpoint in
favour of reversals that leave a decreasing strip: if `r` removes exactly one breakpoint and some
reversal removing exactly one breakpoint leaves a decreasing strip, then so does `r`. Ties among
reversals removing two (or at most zero) breakpoints are unrestricted. -/
def IsGreedyChoice (n : ℕ) (π : List ℤ) (r : ℕ × ℕ) : Prop :=
  IsReversal n r ∧ (∀ r', IsReversal n r' → removal n π r' ≤ removal n π r) ∧
    (removal n π r = 1 →
      (∃ r', IsReversal n r' ∧ removal n π r' = 1 ∧
        HasDecreasingStrip n (revBlock π r'.1 r'.2)) →
      HasDecreasingStrip n (revBlock π r.1 r.2))

/-- A greedy run from `π`: a sequence of reversals, each a greedy choice at a permutation that is
not the identity. -/
inductive GreedyRun (n : ℕ) : List ℤ → List (ℕ × ℕ) → Prop where
  | nil (π : List ℤ) : GreedyRun n π []
  | cons (π : List ℤ) (r : ℕ × ℕ) (rest : List (ℕ × ℕ)) :
      π ≠ identity n → IsGreedyChoice n π r → GreedyRun n (revBlock π r.1 r.2) rest →
        GreedyRun n π (r :: rest)

/-- The result of applying the reversals `rs` in order to `π`. -/
def applyAll (π : List ℤ) (rs : List (ℕ × ℕ)) : List ℤ :=
  rs.foldl (fun l r => revBlock l r.1 r.2) π

/-- **The greedy algorithm sorts within `φ(π)` reversals** (Kececioglu–Sankoff 1995,
Theorem 1). For every unsigned permutation `π` of `1, …, n` (`UValid n π`), every greedy run
from `π` has at most `ubreaks n π` reversals, and some greedy run from `π` ends at the
identity.

Source: J. Kececioglu and D. Sankoff, Algorithmica 13 (1995) 180-210, Theorem 1.

Source: J. Kececioglu and D. Sankoff, author's copy of the same paper (revised 19 February 1993),
Theorem 1, p. 8, <https://www.cs.arizona.edu/~kece/Research/papers/KS95.ps>. -/
theorem_wanted greedyRun_length_le_and_sorts (n : ℕ) {π : List ℤ} (hπ : UValid n π) :
    (∀ rs, GreedyRun n π rs → rs.length ≤ ubreaks n π) ∧
      ∃ rs, GreedyRun n π rs ∧ applyAll π rs = identity n

end WantedExt.Biology.ComputationalBiology.GreedyReversalWanted
