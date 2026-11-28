/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMATIC NUMBER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT3] DOMATIC NUMBER
(transformation from 3SAT, credited there to unpublished work of Garey, Johnson,
and Tarjan);
H. Kaplan and R. Shamir, "The domatic number problem on some perfect graph
families", Information Processing Letters 49 (1994), 51-56,
doi:10.1016/0020-0190(94)90054-X (a published proof, already for split graphs
and for bipartite graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DomaticNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DomaticNumber

/-!
# DOMATIC NUMBER is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is the domatic
number of `G` at least `K`, i.e. can `V` be partitioned into `k ≥ K` disjoint sets
`V₁, ..., Vₖ` such that each `Vᵢ` is a dominating set for `G` (every vertex lies in `Vᵢ` or is
adjacent to a vertex of `Vᵢ`)?

The partition is given by the map `c : V → Fin k` sending each vertex to the index of its
block, so `Vⱼ = c⁻¹(j)`; "dominating set" is `SimpleGraph.IsDominating`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DOMATIC NUMBER is NP-complete.** Source: Garey and Johnson (1979), [GT3];
Kaplan and Shamir (1994). -/
public theorem_wanted domaticNumber_npComplete :
    domaticNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L domaticNumberDec

end MetaMathlibExt.Complexity.NPComplete.DomaticNumber
