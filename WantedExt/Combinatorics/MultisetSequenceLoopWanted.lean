/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multiset inventory sequence always reaches a short loop
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Sort
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.MultisetSequenceLoopWanted

/-! Source record `OPG-37226`, ported from the Open Problem Garden entry
"Sequence defined on multisets"
(http://www.openproblemgarden.org/op/a_sequence_defined_on_multisets).

Starting from a `2 × n` array whose first row lists distinct increasing
positive integers and whose second row holds arbitrary positive integers,
each step replaces the array by the sorted list of all integers occurring
anywhere in it together with their total multiplicities. The conjecture
asserts the process always reaches a loop of one, two, or three arrays.
Multiplicities are counted across both rows of the array. -/

/-- **Inventory step.** The inventory step sends a pair of finite lists of natural numbers (the two
rows of an array) to the pair consisting of the increasing list of the distinct numbers occurring
in either list and the list of how many times each of these numbers occurs in the two lists
together. -/
def step : List ℕ × List ℕ → List ℕ × List ℕ := fun (keys, mults) =>
  let all := keys ++ mults
  let vals := all.toFinset.sort (· ≤ ·)
  (vals, vals.map (fun v => all.count v))

/-- **Inventory loop conjecture.** Let $a_1 < \dots < a_n$ and $b_1, \dots, b_n$ be positive
integers, and iterate the inventory step starting from the pair of rows $(a_1, \dots, a_n)$ and
$(b_1, \dots, b_n)$, where the inventory step replaces a pair of rows by the increasing list of the
distinct integers occurring in either row together with the list of the number of times each of
them occurs in the two rows combined. Then there are a natural number $t$ and a
$p \in \{1, 2, 3\}$ such that the $(t + p)$-th iterate equals the $t$-th iterate. -/
def conjecture : Prop :=
  ∀ keys mults : List ℕ, keys.Pairwise (· < ·) →
    (∀ a ∈ keys, 0 < a) → (∀ b ∈ mults, 0 < b) →
    keys.length = mults.length →
    ∃ t p : ℕ, 1 ≤ p ∧ p ≤ 3 ∧
      (step^[t + p]) (keys, mults) = (step^[t]) (keys, mults)

/-- **Inventory sequences end in short loops.** Let $a_1 < \dots < a_n$ and $b_1, \dots, b_n$ be
positive integers, and iterate the inventory step starting from the pair of rows
$(a_1, \dots, a_n)$ and $(b_1, \dots, b_n)$, where the inventory step replaces a pair of rows by the
increasing list of the distinct integers occurring in either row together with the list of the
number of times each of them occurs in the two rows combined. Then there are a natural number
$t$ and a $p \in \{1, 2, 3\}$ such that the $(t + p)$-th iterate equals the $t$-th iterate.

Resolved in the affirmative: the process is the counting (inventory) map on multisets. Bronstein
and Fraenkel proved that every start is ultimately periodic, and the enumeration of all cycles
(Sauerberg and Shu, re-derived by Cain and Enin) shows that every cycle has length 1, 2 or 3.

Source:
V. Bronstein and A. S. Fraenkel, On a curious property of counting sequences, Amer. Math.
Monthly 101 (1994), https://doi.org/10.1080/00029890.1994.11996991; J. Sauerberg and L. Shu, The
long and the short on counting sequences, Amer. Math. Monthly 104 (1997),
https://doi.org/10.1080/00029890.1997.11990642; O. M. Cain and S. T. Enin, Inventory loops (i.e.
counting sequences) have pre-period 2 max S_1 + 60, arXiv:2004.00209 (2020),
https://arxiv.org/abs/2004.00209. Moved from
`OpenConjectures/Combinatorics/MultisetSequenceLoop`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.MultisetSequenceLoopWanted
