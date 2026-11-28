/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR SUPPORT OF A HYPERGRAPH (PLANAR VENN DIAGRAM): definitions

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

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HypergraphPlanarSupport

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

end MetaMathlibExt.Complexity.NPComplete.HypergraphPlanarSupport
