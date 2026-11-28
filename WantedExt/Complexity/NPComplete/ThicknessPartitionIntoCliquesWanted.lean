/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES for graphs of thickness at most k is NP-complete, for every fixed k ≥ 1

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES;
M. R. Cerioli, L. Faria, T. O. Ferreira, C. A. J. Martinhon, F. Protti and B. Reed,
"Partition into cliques for cubic graphs: Planar case, complexity and approximation", Discrete
Applied Mathematics 156(12) (2008), 2270-2278, doi:10.1016/j.dam.2007.10.015 (NP-complete for
planar cubic graphs);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (PARTITION INTO CLIQUES on planar and on thickness-`k`
graphs: NP-complete, citing F. Berman, D. S. Johnson, F. T. Leighton, P. W. Shor and L. Snyder,
"Generalized planar matching", manuscript, 1985).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThicknessPartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThicknessPartitionIntoCliques

/-!
# PARTITION INTO CLIQUES for graphs of thickness at most k is NP-complete, for every fixed k ≥ 1

Fix `k`. INSTANCE: a graph `G = (V, E)` of thickness at most `k` and a positive integer
`K ≤ |V|`. QUESTION: can `V` be partitioned into at most `K` disjoint sets each of which induces
a clique?

This is PARTITION INTO CLIQUES ([GT15], `PartitionIntoCliquesDefs`) restricted to graphs of
thickness at most `k`. Planar graphs are exactly the graphs of thickness at most `1`, and
Cerioli et al. (2008) prove PARTITION INTO CLIQUES NP-complete already for planar cubic graphs
(the repository's `PartitionIntoCliquesCubicPlanarWanted`). A planar graph has thickness at most
`k` for every `k ≥ 1` (put every edge in one class), so the problem is NP-complete for every fixed
`k ≥ 1`, which is the theorem below (one decision problem per `k`). Johnson's Table 1 records the
planar and the thickness-`k` entries (`k` fixed) as NP-complete.

The instance, its well-formedness (simple edge list, `0 < K ≤ |V|`) and the question are those of
`PartitionIntoCliquesDefs` (`PartitionIntoCliques.PartitionIntoCliquesInstance`;
`PartitionIntoCliques.PartitionIntoCliquesFeasible`: for some `k' ≤ K`, a map to `Fin k'` whose
blocks are cliques, Mathlib's `SimpleGraph.IsClique`).

Thickness: a graph has thickness at most `k` when its edges can be partitioned into `k` classes
each spanning a planar subgraph on all the vertices. This is the question of `GraphThicknessWanted`
(GRAPH THICKNESS, Mansfield 1983) for the bound `k`, reused unchanged as
`GraphThickness.GraphThicknessFeasible (n, E, k)`: a map `f` from the edges to `Fin k` whose classes
`GraphThickness.edgeClass` each give a graph satisfying the shared planarity predicate
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by Fáry's theorem, planarity of
finite simple graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO CLIQUES for graphs of thickness at most `k` is NP-complete, for every fixed
`k ≥ 1`.** Source: Garey and Johnson (1979), [GT15]; Cerioli et al. (2008); Johnson (1985), Table 1.
-/
public theorem_wanted thicknessPartitionIntoCliques_npComplete (k : ℕ) (hk : 1 ≤ k) :
    thicknessPartitionIntoCliquesDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (thicknessPartitionIntoCliquesDec k)

end MetaMathlibExt.Complexity.NPComplete.ThicknessPartitionIntoCliques
