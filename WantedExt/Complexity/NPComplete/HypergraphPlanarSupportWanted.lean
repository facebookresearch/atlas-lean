/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR SUPPORT OF A HYPERGRAPH (PLANAR VENN DIAGRAM) is NP-complete

Source:
D. S. Johnson and H. O. Pollak, "Hypergraph planarity and the complexity of drawing Venn
diagrams", Journal of Graph Theory 11(3) (1987), 309-325, doi:10.1002/jgt.3190110306 (abstract:
"We conclude by showing that the general problem of determining whether such diagrams exist is
NP-complete.");
K. Buchin, M. van Kreveld, H. Meijer, B. Speckmann and K. Verbeek, "On planar supports for
hypergraphs", Journal of Graph Algorithms and Applications 15(4) (2011), 533-549,
doi:10.7155/jgaa.00237 (abstract: "A graph `G` is a support for a hypergraph `H = (V, S)` if
the vertices of `G` correspond to the vertices of `H` such that for each hyperedge `S_i ∈ S`
the subgraph of `G` induced by `S_i` is connected. `G` is a planar support if it is a support
and planar. Johnson and Pollak proved that it is NP-complete to decide if a given hypergraph
has a planar support.").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HypergraphPlanarSupport

/-!
# PLANAR SUPPORT OF A HYPERGRAPH (PLANAR VENN DIAGRAM) is NP-complete

INSTANCE: a hypergraph `H = (V, C)`.
QUESTION: is there a planar graph `G = (V, E)` such that every hyperedge `c ∈ C` induces a
connected subgraph of `G`?

Such a graph `G` is a planar support of `H` (Buchin et al.); Johnson and Pollak relate it to
drawing the hyperedges as the regions of a Venn-type diagram.
The vertices are `Fin n`, the hyperedges are lists of vertex numbers (a hyperedge is the set of
its entries), and every hyperedge is nonempty (a hyperedge is a nonempty set of vertices). "A
planar graph" is `SimpleGraph.IsPlanar` from `MathlibExt.Combinatorics.SimpleGraph.Planarity`
(a crossing-free straight-line drawing, equivalent to planarity by Fáry's theorem; loops and
parallel edges do not affect connectivity, so simple graphs suffice), and "induces a connected
subgraph" is Mathlib's `SimpleGraph.Connected` for the subgraph of `G` induced on the
hyperedge.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and the list of hyperedges, each a list of
vertex numbers. -/
abbrev HypergraphPlanarSupportInstance := ℕ × List (List ℕ)

/-- The vertex set of a hyperedge. -/
def hyperedgeSet (n : ℕ) (c : List ℕ) : Set (Fin n) :=
  {v | (v : ℕ) ∈ c}

/-- Well-formedness of an instance: every hyperedge is nonempty and lists only vertices
`0, …, n - 1`. -/
def WellFormed (i : HypergraphPlanarSupportInstance) : Prop :=
  ∀ c ∈ i.2, c ≠ [] ∧ ∀ v ∈ c, v < i.1

/-- Some planar graph on the vertices induces a connected subgraph on every hyperedge. -/
def HypergraphPlanarSupportFeasible (i : HypergraphPlanarSupportInstance) : Prop :=
  ∃ G : SimpleGraph (Fin i.1), G.IsPlanar ∧
    ∀ c ∈ i.2, (G.induce (hyperedgeSet i.1 c)).Connected

open Classical in
/-- PLANAR SUPPORT OF A HYPERGRAPH as a decision problem over bitstrings. -/
noncomputable def hypergraphPlanarSupportDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HypergraphPlanarSupportInstance) x with
  | some i => decide (WellFormed i ∧ HypergraphPlanarSupportFeasible i)
  | none => false

/-- **PLANAR SUPPORT OF A HYPERGRAPH (PLANAR VENN DIAGRAM) is NP-complete.** Source: Johnson
and Pollak (1987); Buchin et al. (2011). -/
public theorem_wanted hypergraphPlanarSupport_npComplete :
    hypergraphPlanarSupportDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hypergraphPlanarSupportDec

end MetaMathlibExt.Complexity.NPComplete.HypergraphPlanarSupport
