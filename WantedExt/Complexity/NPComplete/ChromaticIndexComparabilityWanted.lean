/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX for comparability graphs is NP-complete

Source:
L. Cai and J. A. Ellis, "NP-completeness of edge-colouring some restricted graphs", Discrete
Applied Mathematics 30(1) (1991), 15-27, doi:10.1016/0166-218X(91)90010-T;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021
(arXiv:2104.14395), Section 2 ("L. Cai and J. A. Ellis proved that deciding whether χ′(G) = 3 is
NP-complete even for COMPARABILITY graphs and for LINE graphs").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChromaticIndexComparabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexComparability

open EdgeColoring (EdgeColoringInstance EdgeColoringFeasible)

/-!
# CHROMATIC INDEX for comparability graphs is NP-complete

INSTANCE: a comparability graph `G = (V, E)` and a positive integer `K`. QUESTION: is the chromatic
index of `G` at most `K`, i.e. can `E` be partitioned into at most `K` matchings (a proper edge
coloring with at most `K` colors)?

This is CHROMATIC INDEX (`EdgeColoringWanted`) restricted to comparability graphs. Cai and Ellis
(1991) prove that deciding whether a comparability graph has chromatic index 3 is NP-complete
(already for `k`-regular comparability graphs, `k ≥ 3`, stated on `main` as
`ChromaticIndexRegularComparabilityWanted`), so the problem with `K` in the input is NP-complete
on comparability graphs. The instance type (vertex count, edge list, `K`), the parent's
well-formedness (a simple edge list) and the question `EdgeColoringFeasible` (a color below `K`
for every edge, distinct on edges sharing an endpoint) are the parent's; the restriction adds the
repository's comparability predicate `ComparabilityGraphSandwich.IsComparabilityGraph` (the
adjacency is the comparability relation of a strict partial order) of the graph
`Cslib.Complexity.Karp.edgeGraph`, and `0 < K` (Johnson's "positive integer K").

Membership in NP: the coloring is the certificate; comparability graphs are recognized in
polynomial time. Isolated vertices change neither the class nor the answer, so the binary vertex
count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CHROMATIC INDEX for comparability graphs is NP-complete.**
Source: Cai and Ellis (1991); de Figueiredo, de Melo, Sasaki and Silva (2022). -/
public theorem_wanted chromaticIndexComparability_npComplete :
    chromaticIndexComparabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chromaticIndexComparabilityDec

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexComparability
