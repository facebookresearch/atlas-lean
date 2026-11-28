/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIALLY ORDERED KNAPSACK with a tree order is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP12] PARTIALLY ORDERED KNAPSACK,
pp. 247-248 (comment: "General problem is solvable in pseudo-polynomial time if < is a "tree"
partial order [Garey and Johnson, ——].");
D. S. Johnson and K. A. Niemi, "On knapsacks, partitions, and a new dynamic
programming technique for trees", Mathematics of Operations Research 8 (1983),
1-14, doi:10.1287/moor.8.1.1 (abstract: the special case where the order is an out-tree "is
still NP-complete").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TreePartiallyOrderedKnapsackDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreePartiallyOrderedKnapsack

open MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsack
  (PartiallyOrderedKnapsackInstance Precedes PartiallyOrderedKnapsackFeasible)

/-!
# PARTIALLY ORDERED KNAPSACK with a tree order is NP-complete

PARTIALLY ORDERED KNAPSACK ([MP12], `PartiallyOrderedKnapsackWanted`) restricted to instances
whose partial order `<` is a tree order: the order of an out-tree, in which `u' < u` means that
`u'` is a proper ancestor of `u`. INSTANCE: a finite set `U`, a tree partial order `<` on `U`,
for each `u ∈ U` a size `s(u) ∈ ℤ⁺` and a value `v(u) ∈ ℤ⁺`, and positive integers `B` and
`K`. QUESTION: is there a subset `U' ⊆ U` such that if `u ∈ U'` and `u' < u`, then `u' ∈ U'`,
and such that `∑_{u ∈ U'} s(u) ≤ B` and `∑_{u ∈ U'} v(u) ≥ K`?

The instance and the question are those of `PartiallyOrderedKnapsackWanted`; only the
restriction is new, in `WellFormed` (`IsTreeOrder`): the predecessors of every element are
pairwise comparable (each element has at most one immediate predecessor, its parent), and some
element (the root) precedes every other element. The problem is NP-complete in the weak sense
(Johnson and Niemi give a pseudo-polynomial algorithm); numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTIALLY ORDERED KNAPSACK with a tree order is NP-complete.** Source: Garey and Johnson
(1979), [MP12], comment; Johnson and Niemi (1983). -/
public theorem_wanted treePartiallyOrderedKnapsack_npComplete :
    treePartiallyOrderedKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treePartiallyOrderedKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.TreePartiallyOrderedKnapsack
