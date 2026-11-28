/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOPOLARITY on (C₄, …, C₈)-free planar graphs of maximum degree 3 is NP-complete

Source:
V. B. Le and R. Nevries, "Complexity and algorithms for recognizing polar and monopolar
graphs", Theoretical Computer Science 528 (2014), 1-11, doi:10.1016/j.tcs.2014.01.032;
V. B. Le and R. Nevries, "Recognizing polar planar graphs using new results for monopolarity",
ISAAC 2011, Lecture Notes in Computer Science 7074 (2011), 120-129,
doi:10.1007/978-3-642-25591-5_14;
recorded in G. Philip and S. T. Sridhara, "Faster algorithms for graph monopolarity",
arXiv:2410.06337 (2024), Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MonopolarityC4ToC8FreePlanarSubcubicDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonopolarityC4ToC8FreePlanarSubcubic

/-!
# MONOPOLARITY on (C₄, …, C₈)-free planar graphs of maximum degree 3 is NP-complete

INSTANCE: a planar graph `G = (V, E)` in which no vertex has degree exceeding `3` and which has
no induced cycle `Cₖ` with `4 ≤ k ≤ 8`.
QUESTION: is `G` monopolar, that is, can `V` be partitioned into sets `A` and `B` such that `A`
is a stable (independent) set and `G[B]` is a disjoint union of cliques?

Le and Nevries prove monopolarity recognition NP-complete, for each fixed `k ≥ 4`, on planar
graphs of maximum degree 3 without induced `C₄, …, Cₖ`; Philip and Sridhara (Section 1) record
it as: Monopolar Recognition is NP-hard "for each fixed integer k ≥ 4, (ii) on planar graphs of
maximum degree 3 that exclude {C4, . . . , Ck} as induced subgraphs" (citing both Le-Nevries
papers). This module states the case `k = 8`, the ISGCI class
"(C_4,C_5,C_6,C_7,C_8)-free ∩ maximum degree 3 ∩ planar" (gc_1282), where ISGCI lists
Monopolarity as NP-complete with the 2014 paper as reference. Triangles are allowed.

The graph is given by a simple edge list on `Fin n` (`Cslib.Complexity.Karp.edgeGraph`).
Monopolarity is `PartitionIntoCliquesMonopolar.IsMonopolar` from
`WantedExt.Complexity.NPComplete.PartitionIntoCliquesMonopolarWanted`: a set `A` with
`G.IsIndepSet A` whose complement induces a cluster graph
(`ClusterDeletion.IsClusterGraph`: every connected component complete). The class goes in
well-formedness: planarity is the shared MathlibExt predicate `SimpleGraph.IsPlanar` (a
crossing-free straight-line drawing, equivalent to planarity by Fáry's theorem), the degree
bound uses `SimpleGraph.degree`, and "`Cₖ`-free" means, as in ISGCI, that the cycle graph
`SimpleGraph.cycleGraph k` is not an induced subgraph (`SimpleGraph.IsIndContained`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MONOPOLARITY on (C₄, …, C₈)-free planar graphs of maximum degree 3 is NP-complete.**
Source: Le and Nevries (2011, 2014). -/
public theorem_wanted monopolarityC4ToC8FreePlanarSubcubic_npComplete :
    monopolarityC4ToC8FreePlanarSubcubicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L monopolarityC4ToC8FreePlanarSubcubicDec

end MetaMathlibExt.Complexity.NPComplete.MonopolarityC4ToC8FreePlanarSubcubic
