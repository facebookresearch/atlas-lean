/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE COPY FILE ALLOCATION with uniform usages and storage costs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR6] MULTIPLE COPY FILE ALLOCATION,
p. 227, comment: "NP-complete in the strong sense, even if all v ∈ V have the same value of
u(v) and the same value of s(v)", credited there to [Van Sickle and Chandy, 1977], "The
complexity of computer network design problems", listed in the book's bibliography as an
unpublished manuscript.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipleCopyFileAllocationUniformCostsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocationUniformCosts

open MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocation
  (MultipleCopyFileAllocationInstance usage storage MultipleCopyFileAllocationFeasible)

/-!
# MULTIPLE COPY FILE ALLOCATION with uniform usages and storage costs is NP-complete

The problem MULTIPLE COPY FILE ALLOCATION
(`MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocation`), restricted to instances in
which all `v ∈ V` have the same value of `u(v)` and the same value of `s(v)`. INSTANCE: a graph
`G = (V, E)`, for each `v ∈ V` a usage `u(v) ∈ ℤ⁺` and a storage cost `s(v) ∈ ℤ⁺`, all usages
equal and all storage costs equal, and a positive integer `K`. QUESTION: is there a subset
`V' ⊆ V` such that, if for each `v ∈ V` we let `d(v)` denote the number of edges in the shortest
path in `G` from `v` to a member of `V'`, we have `∑_{v ∈ V'} s(v) + ∑_{v ∈ V} d(v) · u(v) ≤ K`?

The instance encoding (the vertex count, the edge list, the list of `(u(v), s(v))` indexed by
vertex, and `K`), the well-formedness conditions of MULTIPLE COPY FILE ALLOCATION and the
question are those of `MultipleCopyFileAllocation`; here additionally any two vertices have the
same usage and the same storage cost. The problem is NP-complete in the strong sense; numbers
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

/-- **MULTIPLE COPY FILE ALLOCATION with uniform usages and storage costs is NP-complete.**
Source: Garey and Johnson (1979), [SR6], comment (Van Sickle and Chandy, 1977). -/
public theorem_wanted multipleCopyFileAllocationUniformCosts_npComplete :
    multipleCopyFileAllocationUniformCostsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleCopyFileAllocationUniformCostsDec

end MetaMathlibExt.Complexity.NPComplete.MultipleCopyFileAllocationUniformCosts
