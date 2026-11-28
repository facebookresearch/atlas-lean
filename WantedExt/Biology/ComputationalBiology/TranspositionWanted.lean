/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sorting by transpositions: the odd-cycle bounds and the transposition diameter

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
are cleared of denominators. Framed permutations, transpositions and sorting within `m` moves
are `WellFormed` and `SortingByTranspositionsFeasible` of
`MetaMathlibExt.Complexity.NPComplete.SortingByTranspositions`, for a list of length `n + 2`.

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

open MetaMathlibExt.Complexity.NPComplete.SortingByTranspositions

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

/-- **Odd-cycle lower bound** (Bafna–Pevzner 1998, Theorem 2.4). Let `p` be a framed
permutation of `1, …, n`: a list of length `n + 2` that `WellFormed (p, m)` makes a permutation
of `[0, 1, …, n + 1]` with first entry `0` and last entry `n + 1`. If at most `m`
transpositions sort `p` (`SortingByTranspositionsFeasible (p, m)`), then
`n + 1 ≤ 2m + c_odd(p)`; that is, `d(p) ≥ (n + 1 - c_odd(p))/2`.

Source: V. Bafna and P. A. Pevzner, SIAM J. Discrete Math. 11 (1998) 224-240, Theorem 2.4.

Source: A. Labarre, *Combinatorial aspects of genome rearrangements and haplotype networks*,
PhD thesis, Université libre de Bruxelles, 2008, Theorem 3.1,
<https://theses.hal.science/tel-00482196v1>. -/
theorem_wanted add_one_le_two_mul_add_oddCycles (n : ℕ) {p : List ℕ} (hlen : p.length = n + 2)
    {m : ℕ} (hp : WellFormed (p, m)) (hm : SortingByTranspositionsFeasible (p, m)) :
    n + 1 ≤ 2 * m + oddCycles n p

/-- **Odd-cycle upper bound on the transposition distance** (implied by Bafna–Pevzner 1998,
Corollary 6.10). Let `p` be a framed permutation of `1, …, n`: a list of length `n + 2` with
`WellFormed (p, 0)` (the bound `0` is not read). Then some number `m` of transpositions sorts `p`
(`SortingByTranspositionsFeasible (p, m)`) with `4m + 3 c_odd(p) ≤ 3(n + 1)`, that is
`m ≤ (3/4)(n + 1 - c_odd(p))`; with Theorem 2.4 this is within a factor `3/2` of `d(p)`.

Source: V. Bafna and P. A. Pevzner, SIAM J. Discrete Math. 11 (1998) 224-240,
Corollary 6.10.

Source: A. Labarre, *Combinatorial aspects of genome rearrangements and haplotype networks*,
PhD thesis, Université libre de Bruxelles, 2008, Theorem 3.4,
<https://theses.hal.science/tel-00482196v1>. -/
theorem_wanted exists_sortsWithin_three_quarters (n : ℕ) {p : List ℕ}
    (hlen : p.length = n + 2) (hp : WellFormed (p, 0)) :
    ∃ m, SortingByTranspositionsFeasible (p, m) ∧ 4 * m + 3 * oddCycles n p ≤ 3 * (n + 1)

/-- **Transposition diameter** (Bafna–Pevzner 1998, Corollary 6.11). Let `p` be a framed
permutation of `1, …, n`: a list of length `n + 2` with `WellFormed (p, 0)` (the bound `0` is not
read). Then some number `m` of transpositions sorts `p` (`SortingByTranspositionsFeasible (p, m)`)
with `4m ≤ 3n`.

Source: V. Bafna and P. A. Pevzner, SIAM J. Discrete Math. 11 (1998) 224-240,
Corollary 6.11.

Source: D. A. Christie, *Genome rearrangement problems*, PhD thesis, University of Glasgow,
1998, Section 1.6, p. 11, <https://theses.gla.ac.uk/74685/>. -/
theorem_wanted exists_sortsWithin_diameter (n : ℕ) {p : List ℕ} (hlen : p.length = n + 2)
    (hp : WellFormed (p, 0)) :
    ∃ m, SortingByTranspositionsFeasible (p, m) ∧ 4 * m ≤ 3 * n

end WantedExt.Biology.ComputationalBiology.TranspositionWanted
