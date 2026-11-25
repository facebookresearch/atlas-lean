/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sorting by transpositions: the odd-cycle bound and the 1.5 guarantee

A permutation `π` of `1, …, n` is framed by `π_0 = 0` and `π_{n+1} = n + 1` and written as the
list `[π_0, π_1, …, π_{n+1}]`. For `1 ≤ i < j < k ≤ n + 1`, the transposition `ρ(i, j, k)`
exchanges the blocks `π_i … π_{j-1}` and `π_j … π_{k-1}`; the transposition distance `d(π)` is
the least number of transpositions that turn `π` into the identity.

The cycle graph `G(π)` has a black edge from `π_i` to `π_{i-1}` for `1 ≤ i ≤ n + 1` and a gray
edge from `v` to `v + 1` for `0 ≤ v ≤ n`; it decomposes uniquely into alternating cycles. Leaving
black edge `i` through the gray edge at `π_{i-1}` leads to the black edge at position
`f(i) = pos(π_{i-1} + 1)`, so the alternating cycles are the cycles of the permutation `f` of
`{1, …, n + 1}`, and the length of a cycle is its number of black edges. A cycle is odd if that
number is odd; `c_odd(π)` counts the odd cycles (fixed points of `f` included).

**Theorem 2.4** (Bafna–Pevzner 1998). `d(π) ≥ (n + 1 - c_odd(π))/2`.

**Corollaries 6.10 and 6.11** (Bafna–Pevzner 1998). Algorithm TransSort sorts `π` with at most
`(3/4)(n + 1 - c_odd(π))` transpositions, so it is a 1.5-approximation; and the transposition
diameter of the permutations of `n` elements is at most `3n/4`.

The corollaries are stated as the existence of sorting sequences of those lengths (the sequences
TransSort produces); the algorithm itself and its `O(n²)` running time are not stated. Bounds
are cleared of denominators.

Sources: V. Bafna and P. A. Pevzner, "Sorting by transpositions", SIAM J. Discrete Math.
11(2):224-240, 1998, doi:10.1137/S089548019528280X, Theorem 2.4 and Corollaries 6.10-6.11.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Complexity.NPComplete.SortingByTranspositionsWanted
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.TranspositionWanted

/-- `p` is a framed permutation of `1, …, n`: a permutation of `[0, 1, …, n + 1]` with first
entry `0` and last entry `n + 1`. -/
def IsFramedPerm (n : ℕ) (p : List ℕ) : Prop :=
  p.Perm (List.range (n + 2)) ∧ p.getD 0 0 = 0 ∧ p.getD (n + 1) 0 = n + 1

/-- A valid transposition `(i, j, k)` of a framed permutation of `1, …, n`:
`1 ≤ i < j < k ≤ n + 1`. -/
def IsValidTransposition (n : ℕ) (o : ℕ × ℕ × ℕ) : Prop :=
  1 ≤ o.1 ∧ o.1 < o.2.1 ∧ o.2.1 < o.2.2 ∧ o.2.2 ≤ n + 1

/-- At most `m` valid transpositions, applied in order, turn `p` into the identity
`[0, 1, …, n + 1]`, so `d(p) ≤ m`. Uses
`MetaMathlibExt.Complexity.NPComplete.SortingByTranspositions.transposition`. -/
def SortsWithin (n : ℕ) (p : List ℕ) (m : ℕ) : Prop :=
  ∃ ops : List (ℕ × ℕ × ℕ), ops.length ≤ m ∧ (∀ o ∈ ops, IsValidTransposition n o) ∧
    ops.foldl (fun l o =>
      MetaMathlibExt.Complexity.NPComplete.SortingByTranspositions.transposition
        l o.1 o.2.1 o.2.2) p = List.range (n + 2)

/-- The successor of black edge `i` in its alternating cycle: the position of `p_{i-1} + 1`. -/
def cycleSucc (p : List ℕ) (i : ℕ) : ℕ :=
  p.idxOf (p.getD (i - 1) 0 + 1)

open Classical in
/-- The black edges in the alternating cycle of black edge `i`, a subset of `{1, …, n + 1}`. -/
noncomputable def cycleOf (n : ℕ) (p : List ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n + 1)).filter fun j => ∃ t, (cycleSucc p)^[t] i = j

open Classical in
/-- `c_odd(p)`: the number of alternating cycles with an odd number of black edges, each counted
once at its least black edge. -/
noncomputable def oddCycles (n : ℕ) (p : List ℕ) : ℕ :=
  ((Finset.Icc 1 (n + 1)).filter fun i =>
    (∀ j ∈ cycleOf n p i, i ≤ j) ∧ Odd (cycleOf n p i).card).card

/-- **Odd-cycle lower bound** (Bafna–Pevzner 1998, Theorem 2.4). For every framed permutation
`p` of `1, …, n` and every `m` such that at most `m` transpositions sort `p`,
`n + 1 ≤ 2m + c_odd(p)`; that is, `d(p) ≥ (n + 1 - c_odd(p))/2`.

Source: V. Bafna and P. A. Pevzner, SIAM J. Discrete Math. 11 (1998) 224-240, Theorem 2.4. -/
theorem_wanted add_one_le_two_mul_add_oddCycles (n : ℕ) {p : List ℕ} (hp : IsFramedPerm n p)
    {m : ℕ} (hm : SortsWithin n p m) :
    n + 1 ≤ 2 * m + oddCycles n p

/-- **The 1.5 guarantee** (Bafna–Pevzner 1998, Corollary 6.10). Every framed permutation `p` of
`1, …, n` can be sorted by some number `m` of transpositions with
`4m + 3 c_odd(p) ≤ 3(n + 1)`, that is `m ≤ (3/4)(n + 1 - c_odd(p))`; with Theorem 2.4 this is
within a factor `3/2` of `d(p)`.

Source: V. Bafna and P. A. Pevzner, SIAM J. Discrete Math. 11 (1998) 224-240,
Corollary 6.10. -/
theorem_wanted exists_sortsWithin_three_quarters (n : ℕ) {p : List ℕ}
    (hp : IsFramedPerm n p) :
    ∃ m, SortsWithin n p m ∧ 4 * m + 3 * oddCycles n p ≤ 3 * (n + 1)

/-- **Transposition diameter** (Bafna–Pevzner 1998, Corollary 6.11). Every framed permutation
`p` of `1, …, n` can be sorted by some number `m` of transpositions with `4m ≤ 3n`.

Source: V. Bafna and P. A. Pevzner, SIAM J. Discrete Math. 11 (1998) 224-240,
Corollary 6.11. -/
theorem_wanted exists_sortsWithin_diameter (n : ℕ) {p : List ℕ} (hp : IsFramedPerm n p) :
    ∃ m, SortsWithin n p m ∧ 4 * m ≤ 3 * n

end WantedExt.Biology.ComputationalBiology.TranspositionWanted
