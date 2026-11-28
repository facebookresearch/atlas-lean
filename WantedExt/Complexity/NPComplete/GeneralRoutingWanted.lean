/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERAL ROUTING is NP-complete

Source:
J. K. Lenstra and A. H. G. Rinnooy Kan, "On general routing problems", Networks 6 (1976),
273-280, doi:10.1002/net.3230060305 (Section 2: the general routing problem, and the theorem
that its special case `Q = ∅`, the rural postman problem, is polynomial complete);
C. S. Orloff, "A fundamental problem in vehicle routing", Networks 4 (1974), 35-64,
doi:10.1002/net.3230040105 (definition of the problem);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM GENERAL ROUTING ("Generalization of ND27" of Garey and Johnson (1979)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeneralRoutingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralRouting

open MetaMathlibExt.Complexity.NPComplete.RuralPostman (RuralPostmanInstance)

/-!
# GENERAL ROUTING is NP-complete

INSTANCE: a graph `G = (V, E)`, a length `l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a subset `E' ⊆ E` of
required edges, a subset `V' ⊆ V` of required vertices, and a positive integer `B`.
QUESTION: is there a tour in `G` that contains every vertex of `V'` and traverses every edge of
`E'`, of total length at most `B`?

This is the general routing problem of Orloff, in the words of Lenstra and Rinnooy Kan: "Given
a graph G = (N,A) with non-negative weights on the arcs, the general routing problem (GRP) is to
find a minimum weight tour containing a subset Q ⊆ N of required nodes and a subset R ⊆ A of
required arcs." It specializes to RURAL POSTMAN when `Q = ∅` (`RuralPostmanWanted`, [ND27]),
which Lenstra and Rinnooy Kan prove polynomial complete, and to the traveling salesman problem
when `Q = N` and `R = ∅`.

As in `RuralPostmanWanted`, a tour is a closed walk that may repeat vertices and edges, and its
length counts every traversal of an edge. The instance is a `RuralPostman` instance (vertex
count, edge list with lengths, required edges, bound `B`) paired with the list of required
vertices; the graph, the edge lengths and the parent's well-formedness conditions are the
parent's, unchanged.

The Crescenzi-Kann entry says the cycle "visits each vertex in V' exactly once"; the sources
above define the problem with a tour that contains each required node, which is what is stated
here.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERAL ROUTING is NP-complete.** Source: Lenstra and Rinnooy Kan (1976); Orloff (1974);
Crescenzi and Kann, MINIMUM GENERAL ROUTING. -/
public theorem_wanted generalRouting_npComplete :
    generalRoutingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L generalRoutingDec

end MetaMathlibExt.Complexity.NPComplete.GeneralRouting
