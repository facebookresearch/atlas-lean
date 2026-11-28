/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RURAL POSTMAN is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND27] RURAL POSTMAN;
J. K. Lenstra and A. H. G. Rinnooy Kan, "On general routing problems",
Networks 6 (1976), 273-280, doi:10.1002/net.3230060305 (Theorem: the rural
postman problem is polynomial complete for undirected and for directed graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RuralPostmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RuralPostman

/-!
# RURAL POSTMAN is NP-complete

INSTANCE: a graph `G = (V, E)`, a length `l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a subset `E' ⊆ E`, and
a positive integer `B`. QUESTION: is there a circuit in `G` that includes each edge in `E'` and
that has total length no more than `B`?

A circuit here is a closed walk that may repeat vertices and edges, as in the source's
"postman's tour (i.e. an undirected cycle traversing each arc in a given subset R ⊆ A at least
once)" (Lenstra and Rinnooy Kan); its length counts every traversal of an edge. It is a Mathlib
`SimpleGraph.Walk v v`, and its total length is the sum of the edge lengths along
`SimpleGraph.Walk.edges` (with repetitions).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RURAL POSTMAN is NP-complete.** Source: Garey and Johnson (1979), [ND27]; Lenstra and
Rinnooy Kan (1976). -/
public theorem_wanted ruralPostman_npComplete :
    ruralPostmanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L ruralPostmanDec

end MetaMathlibExt.Complexity.NPComplete.RuralPostman
