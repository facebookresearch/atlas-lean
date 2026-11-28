/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOPOLARITY on triangle-free planar graphs of maximum degree 3 is NP-complete

Source:
V. B. Le and R. Nevries, "Complexity and algorithms for recognizing polar and monopolar
graphs", Theoretical Computer Science 528 (2014), 1-11, doi:10.1016/j.tcs.2014.01.032.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MonopolarityTriangleFreePlanarSubcubicDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonopolarityTriangleFreePlanarSubcubic

/-!
# MONOPOLARITY on triangle-free planar graphs of maximum degree 3 is NP-complete

INSTANCE: a triangle-free planar graph `G = (V, E)` in which no vertex has degree exceeding `3`.
QUESTION: is `G` monopolar, that is, can `V` be partitioned into sets `A` and `B` such that `A`
is a stable (independent) set and `G[B]` is a disjoint union of cliques?

Le and Nevries (2014, abstract): a graph is monopolar if "its vertex set admits a partition
V = A ∪ B such that A induces a complete multipartite graph and B the complement of a complete
multipartite graph", with "A ... a stable set"; "we show that this problem is NP-complete for
triangle-free planar graphs of maximum degree three".

The graph is given by a simple edge list on `Fin n` (`Cslib.Complexity.Karp.edgeGraph`).
Monopolarity is `PartitionIntoCliquesMonopolar.IsMonopolar` from
`WantedExt.Complexity.NPComplete.PartitionIntoCliquesMonopolarWanted`: a set `A` with
`G.IsIndepSet A` whose complement induces a cluster graph
(`ClusterDeletion.IsClusterGraph`: every connected component complete), which is the complement
of a complete multipartite graph. The class goes in well-formedness: planarity is the shared
MathlibExt predicate `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, equivalent
to planarity by Fáry's theorem), triangle-free is Mathlib's `CliqueFree 3`, and the degree bound
uses `SimpleGraph.degree`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MONOPOLARITY on triangle-free planar graphs of maximum degree 3 is NP-complete.** Source:
Le and Nevries (2014). -/
public theorem_wanted monopolarityTriangleFreePlanarSubcubic_npComplete :
    monopolarityTriangleFreePlanarSubcubicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L monopolarityTriangleFreePlanarSubcubicDec

end MetaMathlibExt.Complexity.NPComplete.MonopolarityTriangleFreePlanarSubcubic
