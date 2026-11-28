/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITY ASSIGNMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR7] CAPACITY ASSIGNMENT
(p. 227; transformation from SUBSET SUM), credited there to [Van Sickle and Chandy, 1977],
"The complexity of computer network design problems", listed in the book's bibliography as an
unpublished manuscript.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CapacityAssignmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacityAssignment

/-!
# CAPACITY ASSIGNMENT is NP-complete

INSTANCE: a set `C` of communication links, a set `M ⊆ ℤ⁺` of capacities, a cost function
`g : C × M → ℤ⁺` and a delay penalty function `d : C × M → ℤ⁺` such that, for all `c ∈ C` and
`i < j ∈ M`, `g(c, i) ≤ g(c, j)` and `d(c, i) ≥ d(c, j)`, and positive integers `K` and `J`.
QUESTION: is there an assignment `σ : C → M` such that the total cost `∑_{c ∈ C} g(c, σ(c))`
does not exceed `K` and such that the total delay penalty `∑_{c ∈ C} d(c, σ(c))` does not exceed
`J`?

The links are `0, …, |C| - 1`; the capacities are listed without repetition, and `σ` picks for
each link a position in that list. For each link the instance lists one pair
`(g(c, x), d(c, x))` per capacity `x`, in the order of the capacity list. The problem is
NP-complete in the ordinary sense and solvable in pseudo-polynomial time; numbers use the binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CAPACITY ASSIGNMENT is NP-complete.** Source: Garey and Johnson (1979), [SR7] (Van Sickle
and Chandy, 1977). -/
public theorem_wanted capacityAssignment_npComplete :
    capacityAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L capacityAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.CapacityAssignment
