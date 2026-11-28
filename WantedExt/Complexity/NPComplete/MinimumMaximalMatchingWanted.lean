/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MAXIMAL MATCHING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT10] MINIMUM MAXIMAL
MATCHING;
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on
Applied Mathematics 38 (1980), 364-372, doi:10.1137/0138030.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumMaximalMatchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatching

/-!
# MINIMUM MAXIMAL MATCHING is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: is there a subset
`E' ⊆ E` with `|E'| ≤ K` such that `E'` is a maximal matching, that is, no two edges of `E'`
share a common endpoint and every edge in `E - E'` shares a common endpoint with some edge
of `E'`?

The matching `E'` is a Mathlib subgraph `M` of `G` with `M.IsMatching`; its edge set is
`M.edgeSet ⊆ E`. Under `WellFormed` the edge list has one entry per edge, so its length is
`|E|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM MAXIMAL MATCHING is NP-complete.** Source: Garey and Johnson (1979), [GT10];
Yannakakis and Gavril (1980). -/
public theorem_wanted minimumMaximalMatching_npComplete :
    minimumMaximalMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumMaximalMatchingDec

end MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatching
