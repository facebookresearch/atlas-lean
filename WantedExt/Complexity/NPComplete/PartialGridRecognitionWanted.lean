/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL GRID GRAPH RECOGNITION is NP-complete

Source:
V. G. P. de Sá, G. D. da Fonseca, R. C. S. Machado and C. M. H. de Figueiredo, "Complexity
dichotomy on partial grid recognition", Theoretical Computer Science 412 (2011), 2370-2379,
doi:10.1016/j.tcs.2011.01.018;
S. N. Bhatt and S. S. Cosmadakis, "The complexity of minimizing wire lengths in VLSI layouts",
Information Processing Letters 25 (1987), 263-267, doi:10.1016/0020-0190(87)90173-6;
ISGCI (https://www.graphclasses.org/classes/gc_440.html), problem "Recognition" on partial grid
graphs: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitLengthTreeGridEmbeddingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialGridRecognition

open UnitLengthTreeGridEmbedding (UnitLengthTreeGridEmbeddingInstance Graph
  UnitLengthTreeGridEmbeddingFeasible)

/-!
# PARTIAL GRID GRAPH RECOGNITION is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` a partial grid graph, that is, isomorphic to a (not necessarily induced)
subgraph of the square grid; equivalently, can `G` be embedded in the grid with all edges of
unit length?

ISGCI: "A graph is a partial grid iff it is an arbitrary subgraph (not necessarily induced) of a
grid." De Sá, da Fonseca, Machado and de Figueiredo (2011), abstract: "Deciding whether a graph
can be embedded in a grid using only unit-length edges is NP-complete, even when restricted to
binary trees." The tree case goes back to Bhatt and Cosmadakis (1987); the restriction to trees
is `UnitLengthTreeGridEmbeddingWanted`. Membership in NP: an embedding of an `n`-vertex
graph can be translated so that every connected component lies in an `n × n` box and the
components in disjoint boxes, so it is a polynomial-size certificate.

This is `UnitLengthTreeGridEmbeddingWanted` without the restriction to trees: the same instance
type and graph (`Cslib.Complexity.Karp.edgeGraph`), the simple-edge-list part of its
well-formedness, and its question `UnitLengthTreeGridEmbeddingFeasible`, reused unchanged:
Mathlib's `SimpleGraph.IsContained` (an injective placement of the vertices on grid points
sending every edge to a grid edge) into MathlibExt's infinite square grid
`StatMech.Lattice.hypercubicLattice 2` (sites `Fin 2 → ℤ`, adjacent at `ℓ¹` distance one). The
image of a finite graph lies in a finite grid, so this is the class of subgraphs of grids.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range); the graph need not be
a tree. -/
def WellFormed (i : UnitLengthTreeGridEmbeddingInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

open Classical in
/-- PARTIAL GRID GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def partialGridRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitLengthTreeGridEmbeddingInstance) x with
  | some i => decide (WellFormed i ∧ UnitLengthTreeGridEmbeddingFeasible i)
  | none => false

/-- **PARTIAL GRID GRAPH RECOGNITION is NP-complete.** Source: de Sá, da Fonseca, Machado and de
Figueiredo (2011); Bhatt and Cosmadakis (1987). -/
public theorem_wanted partialGridRecognition_npComplete :
    partialGridRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partialGridRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.PartialGridRecognition
