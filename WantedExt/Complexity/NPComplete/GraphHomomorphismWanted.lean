/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH HOMOMORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), GRAPH HOMOMORPHISM; P.
Hell and J. Nesetril, "On the complexity of H-coloring" (1990).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphHomomorphismDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphHomomorphism

/-!
# GRAPH HOMOMORPHISM is NP-complete

Two undirected graphs `G` and `H`. The question is whether there is a homomorphism `G → H`: a
map from the vertices of `G` to those of `H` sending every edge of `G` to an edge of `H`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH HOMOMORPHISM is NP-complete.** The decision problem GRAPH HOMOMORPHISM belongs to NP,
and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), GRAPH HOMOMORPHISM; P. Hell and J. Nesetril, "On the
complexity of H-coloring" (1990). -/
public theorem_wanted graphHomomorphism_npComplete :
    graphHomomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphHomomorphismDec

end MetaMathlibExt.Complexity.NPComplete.GraphHomomorphism
