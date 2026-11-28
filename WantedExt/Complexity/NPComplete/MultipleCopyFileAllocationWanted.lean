/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE COPY FILE ALLOCATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR6] MULTIPLE COPY FILE ALLOCATION
(p. 227; transformation from VERTEX COVER), credited there to [Van Sickle and Chandy, 1977],
"The complexity of computer network design problems", listed in the book's bibliography as an
unpublished manuscript.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipleCopyFileAllocationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocation

/-!
# MULTIPLE COPY FILE ALLOCATION is NP-complete

INSTANCE: a graph `G = (V, E)`, for each `v ∈ V` a usage `u(v) ∈ ℤ⁺` and a storage cost
`s(v) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there a subset `V' ⊆ V` such that, if for
each `v ∈ V` we let `d(v)` denote the number of edges in the shortest path in `G` from `v` to a
member of `V'`, we have `∑_{v ∈ V'} s(v) + ∑_{v ∈ V} d(v) · u(v) ≤ K`?

`d(v)` exists only when `v` can reach `V'`; a vertex that cannot (for instance, any vertex when
`V' = ∅`) has no such path, and the subset `V'` does not qualify. The statement assigns each
vertex `v` a copy `c(v) ∈ V'` reachable from `v` and charges `dist(v, c(v))` (Mathlib's
`SimpleGraph.dist`, the number of edges of a shortest walk); since every term is non-negative,
some assignment meets the bound exactly when the nearest copies do, so this is the source's
condition with `d(v)` the minimum of `dist(v, w)` over the members `w ∈ V'` that `v` can reach
(Mathlib's `dist` is `0` for an unreachable pair, so unreachable members are excluded). Numbers
use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIPLE COPY FILE ALLOCATION is NP-complete.** Source: Garey and Johnson (1979), [SR6]
(Van Sickle and Chandy, 1977). -/
public theorem_wanted multipleCopyFileAllocation_npComplete :
    multipleCopyFileAllocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleCopyFileAllocationDec

end MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocation
