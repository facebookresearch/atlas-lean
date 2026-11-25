/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The greedy breakpoint algorithm for unsigned sorting by reversals

An unsigned permutation `π` of `1, …, n` is framed by `π_0 = 0` and `π_{n+1} = n + 1` and
written as the list `[π_0, …, π_{n+1}]`. A reversal `(i, j)` with `1 ≤ i < j ≤ n` reverses the
block `π_i … π_j`. A breakpoint is an adjacent pair `(π_t, π_{t+1})`, `0 ≤ t ≤ n`, whose values
do not differ by one; `φ(π)` is the number of breakpoints. A strip is a maximal run of positions
without breakpoints; a strip is decreasing if its values decrease, where a single element is a
decreasing strip unless it is `π_0` or `π_{n+1}`. `OPT(π)` is the least number of reversals that
sort `π`.

The greedy algorithm repeatedly chooses a reversal removing the most breakpoints, preferring,
among those, one whose result has a decreasing strip.

**Theorem 1** (Kececioglu–Sankoff 1995). The greedy algorithm sorts every permutation `π` with
at most `φ(π)` reversals.

**Corollary 1** (Kececioglu–Sankoff 1995). Since a reversal removes at most two breakpoints,
`OPT(π) ≥ φ(π)/2`, so the greedy algorithm uses at most `2 OPT(π)` reversals.

A greedy run is any sequence of reversals in which each reversal is a greedy choice at a
permutation other than the identity; every choice the algorithm may make is covered. Theorem 1
is stated as: every greedy run has at most `φ(π)` reversals (so every greedy run can be continued
until it reaches the identity), and some greedy run reaches the identity. The `O(n²)` time and
`O(n)` space bounds, and the paper's exact branch-and-bound algorithm, are not stated.

Sources: J. Kececioglu and D. Sankoff, "Exact and approximation algorithms for sorting by
reversals, with application to genome rearrangement", Algorithmica 13(1-2):180-210, 1995,
doi:10.1007/BF01188586, Theorem 1 and Corollary 1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Int.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.GreedyReversalWanted

/-- `F` is a framed permutation of `1, …, n`: a permutation of `[0, 1, …, n + 1]` with first
entry `0` and last entry `n + 1`. -/
def IsFramedPerm (n : ℕ) (F : List ℕ) : Prop :=
  F.Perm (List.range (n + 2)) ∧ F.getD 0 0 = 0 ∧ F.getD (n + 1) 0 = n + 1

/-- The identity framed permutation `[0, 1, …, n + 1]`. -/
def identity (n : ℕ) : List ℕ :=
  List.range (n + 2)

/-- The values `x` and `y` differ by one. -/
def IsAdj (x y : ℕ) : Prop :=
  x + 1 = y ∨ y + 1 = x

instance (x y : ℕ) : Decidable (IsAdj x y) := by unfold IsAdj; infer_instance

/-- The number `φ(F)` of breakpoints: positions `t` with `t + 1 < |F|` whose values `F_t` and
`F_{t+1}` do not differ by one. -/
def breakpoints (F : List ℕ) : ℕ :=
  ((List.range (F.length - 1)).filter fun t => ¬ IsAdj (F.getD t 0) (F.getD (t + 1) 0)).length

/-- A reversal `(i, j)` of a framed permutation of `1, …, n`: `1 ≤ i < j ≤ n`. -/
def IsReversal (n : ℕ) (r : ℕ × ℕ) : Prop :=
  1 ≤ r.1 ∧ r.1 < r.2 ∧ r.2 ≤ n

/-- Reverse the block in positions `i, …, j`. -/
def reversal (F : List ℕ) (r : ℕ × ℕ) : List ℕ :=
  F.take r.1 ++ ((F.drop r.1).take (r.2 + 1 - r.1)).reverse ++ F.drop (r.2 + 1)

/-- The number of breakpoints removed by the reversal `r` (negative if it creates some). -/
def removal (F : List ℕ) (r : ℕ × ℕ) : ℤ :=
  (breakpoints F : ℤ) - breakpoints (reversal F r)

/-- The framed permutation `F` of `1, …, n` has a decreasing strip: some position `1 ≤ t ≤ n`
is a strip of a single element (breakpoints on both sides), or has `F_{t+1} + 1 = F_t` (it lies
in a decreasing strip of length at least two). -/
def HasDecreasingStrip (n : ℕ) (F : List ℕ) : Prop :=
  ∃ t, 1 ≤ t ∧ t ≤ n ∧
    ((¬ IsAdj (F.getD (t - 1) 0) (F.getD t 0) ∧ ¬ IsAdj (F.getD t 0) (F.getD (t + 1) 0)) ∨
      F.getD (t + 1) 0 + 1 = F.getD t 0)

/-- `r` is a greedy choice at `F`: a reversal removing the most breakpoints among all reversals,
whose result has a decreasing strip whenever some reversal removing equally many breakpoints
leaves a decreasing strip. -/
def IsGreedyChoice (n : ℕ) (F : List ℕ) (r : ℕ × ℕ) : Prop :=
  IsReversal n r ∧ (∀ r', IsReversal n r' → removal F r' ≤ removal F r) ∧
    ((∃ r', IsReversal n r' ∧ removal F r' = removal F r ∧
      HasDecreasingStrip n (reversal F r')) → HasDecreasingStrip n (reversal F r))

/-- A greedy run from `F`: a sequence of reversals, each a greedy choice at a permutation that
is not the identity. -/
inductive GreedyRun (n : ℕ) : List ℕ → List (ℕ × ℕ) → Prop where
  | nil (F : List ℕ) : GreedyRun n F []
  | cons (F : List ℕ) (r : ℕ × ℕ) (rest : List (ℕ × ℕ)) :
      F ≠ identity n → IsGreedyChoice n F r → GreedyRun n (reversal F r) rest →
        GreedyRun n F (r :: rest)

/-- The result of applying the reversals `rs` in order to `F`. -/
def applyAll (F : List ℕ) (rs : List (ℕ × ℕ)) : List ℕ :=
  rs.foldl reversal F

/-- **The greedy algorithm sorts within `φ(π)` reversals** (Kececioglu–Sankoff 1995,
Theorem 1). For every framed permutation `F` of `1, …, n`, every greedy run from `F` has at
most `φ(F)` reversals, and some greedy run from `F` ends at the identity.

Source: J. Kececioglu and D. Sankoff, Algorithmica 13 (1995) 180-210, Theorem 1. -/
theorem_wanted greedyRun_length_le_and_sorts (n : ℕ) {F : List ℕ} (hF : IsFramedPerm n F) :
    (∀ rs, GreedyRun n F rs → rs.length ≤ breakpoints F) ∧
      ∃ rs, GreedyRun n F rs ∧ applyAll F rs = identity n

/-- **The greedy algorithm is a 2-approximation** (Kececioglu–Sankoff 1995, Corollary 1). For
every framed permutation `F` of `1, …, n`, every greedy run `rs` from `F` and every sequence
`ops` of reversals sorting `F`, `|rs| ≤ 2 |ops|`.

Source: J. Kececioglu and D. Sankoff, Algorithmica 13 (1995) 180-210, Corollary 1. -/
theorem_wanted greedyRun_length_le_two_mul (n : ℕ) {F : List ℕ} (hF : IsFramedPerm n F)
    {rs : List (ℕ × ℕ)} (hrs : GreedyRun n F rs) {ops : List (ℕ × ℕ)}
    (hops : ∀ r ∈ ops, IsReversal n r) (hsort : applyAll F ops = identity n) :
    rs.length ≤ 2 * ops.length

end WantedExt.Biology.ComputationalBiology.GreedyReversalWanted
