/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL 3D GRID GRAPH RECOGNITION is NP-complete

Source:
V. G. P. de Sá, G. D. da Fonseca, R. C. S. Machado and C. M. H. de Figueiredo, "Complexity
dichotomy on partial grid recognition", Theoretical Computer Science 412 (2011), 2370-2379,
doi:10.1016/j.tcs.2011.01.018 (abstract: "the three-dimensional version of the problem was for
the first time proven to be NP-complete");
ISGCI (https://www.graphclasses.org/classes/gc_850.html), problem "Recognition" on partial 3d
grid graphs: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartialThreeDimensionalGridRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialThreeDimensionalGridRecognition

open UnitLengthTreeGridEmbedding (UnitLengthTreeGridEmbeddingInstance Graph)

/-!
# PARTIAL 3D GRID GRAPH RECOGNITION is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` a partial 3d grid graph, that is, isomorphic to a (not necessarily induced)
subgraph of the three-dimensional grid; equivalently, can `G` be embedded in the 3d grid with
all edges of unit length?

ISGCI: "A graph is a partial 3d grid iff it is an arbitrary subgraph (not necessarily induced)
of a 3d grid." De Sá, da Fonseca, Machado and de Figueiredo (2011) prove the recognition problem
for partial grids (unit-length grid embedding) NP-complete in two and, for the first time, in
three dimensions. Membership in NP: an embedding of an `n`-vertex graph can be translated so
that every connected component lies in an `n × n × n` box and the components in disjoint boxes,
so it is a polynomial-size certificate. Vertices outside the edge list are isolated and take
unused grid points, so the check runs on the non-isolated vertices and the binary vertex count
does not make the problem succinct.

This is the three-dimensional version of
`WantedExt.Complexity.NPComplete.PartialGridRecognitionWanted`: the same instance type and graph
(`Cslib.Complexity.Karp.edgeGraph`) and the same well-formedness
(`PartialGridRecognition.WellFormed`, a simple edge list), with the question asking for
Mathlib's `SimpleGraph.IsContained` (an injective placement of the vertices on grid points
sending every edge to a grid edge) into MathlibExt's infinite cubic grid
`StatMech.Lattice.hypercubicLattice 3` (sites `Fin 3 → ℤ`, adjacent at `ℓ¹` distance one) in
place of `hypercubicLattice 2`. The image of a finite graph lies in a finite grid, so this is
the class of subgraphs of 3d grids.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTIAL 3D GRID GRAPH RECOGNITION is NP-complete.** Source: de Sá, da Fonseca, Machado and
de Figueiredo (2011). -/
public theorem_wanted partialThreeDimensionalGridRecognition_npComplete :
    partialThreeDimensionalGridRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partialThreeDimensionalGridRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.PartialThreeDimensionalGridRecognition
