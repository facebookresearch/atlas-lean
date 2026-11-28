/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIALLY ORDERED KNAPSACK is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP12] PARTIALLY
ORDERED KNAPSACK;
D. S. Johnson and K. A. Niemi, "On knapsacks, partitions, and a new dynamic
programming technique for trees", Mathematics of Operations Research 8 (1983),
1-14, doi:10.1287/moor.8.1.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartiallyOrderedKnapsackDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsack

/-!
# PARTIALLY ORDERED KNAPSACK is NP-complete

INSTANCE: a finite set `U`, a partial order `<` on `U`, for each `u ∈ U` a size `s(u) ∈ ℤ⁺` and a
value `v(u) ∈ ℤ⁺`, and positive integers `B` and `K`. QUESTION: is there a subset `U' ⊆ U` such
that if `u ∈ U'` and `u' < u`, then `u' ∈ U'`, and such that `∑_{u ∈ U'} s(u) ≤ B` and
`∑_{u ∈ U'} v(u) ≥ K`?

The elements are `Fin n`, `n` the length of the list of (size, value) pairs. The order is given
as the list of its pairs `(a, b)`, meaning `uₐ < u_b`; `WellFormed` requires the relation it
lists to be a strict partial order, Mathlib's `IsStrictOrder` (irreflexive and transitive).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTIALLY ORDERED KNAPSACK is NP-complete.** Source: Garey and Johnson (1979), [MP12];
Johnson and Niemi (1983). -/
public theorem_wanted partiallyOrderedKnapsack_npComplete :
    partiallyOrderedKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partiallyOrderedKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsack
