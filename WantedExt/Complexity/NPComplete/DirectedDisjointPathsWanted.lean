/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED DISJOINT PATHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), DISJOINT PATHS; S.
Fortune, J. Hopcroft, and J. Wyllie, "The directed subgraph homeomorphism problem" (1980).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedDisjointPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedDisjointPaths

/-!
# DIRECTED DISJOINT PATHS is NP-complete

A directed graph and a list of source-target pairs. The question is whether there are pairwise
vertex-disjoint directed paths joining each pair, with paths simple and endpoints matching the
pairs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DIRECTED DISJOINT PATHS is NP-complete.** The decision problem DIRECTED DISJOINT PATHS
belongs to NP, and every decision problem in NP reduces to it by a polynomial-time many-one
reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), DISJOINT PATHS; S. Fortune, J. Hopcroft, and J.
Wyllie, "The directed subgraph homeomorphism problem" (1980). -/
public theorem_wanted directedDisjointPaths_npComplete :
    directedDisjointPathsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedDisjointPathsDec

end MetaMathlibExt.Complexity.NPComplete.DirectedDisjointPaths
