/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH THICKNESS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN3] GRAPH
GENUS (comment: "Does `G` have thickness `K` or less" is listed as an open
generalization of planarity);
A. Mansfield, "Determining the thickness of graphs is NP-hard", Mathematical
Proceedings of the Cambridge Philosophical Society 93 (1983), 9-23,
doi:10.1017/S030500410006028X.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphThickness

/-!
# GRAPH THICKNESS is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`. QUESTION: does `G` have thickness
`K` or less, i.e., can `E` be partitioned into `K` disjoint sets `E₁, E₂, …, E_K` such that
each subgraph `Gᵢ = (V, Eᵢ)` is planar?

The partition is a map `f` from the edges (positions in the edge list) to `Fin K`, with
`Eᵢ = f⁻¹(i)`; under `WellFormed` the edge list has no duplicate edges in either orientation,
so positions are edges. `Gᵢ = (V, Eᵢ)` is the spanning subgraph `edgeGraph n Eᵢ` on all `n`
vertices. Planarity is the shared MathlibExt predicate `SimpleGraph.IsPlanar` (a crossing-free
straight-line drawing); by Fáry's theorem this is planarity for finite simple graphs. Each
`Gᵢ` has its own drawing.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev GraphThicknessInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : GraphThicknessInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- The edges `Eᵢ = f⁻¹(c)` of class `c` of an assignment `f` of the edges to `K` classes. -/
def edgeClass (i : GraphThicknessInstance) (f : Fin i.2.1.length → Fin i.2.2) (c : Fin i.2.2) :
    List (ℕ × ℕ) :=
  ((List.finRange i.2.1.length).filter fun e => f e = c).map i.2.1.get

/-- The edges can be partitioned into `K` classes, each spanning a planar subgraph
`(V, Eᵢ)`. -/
def GraphThicknessFeasible (i : GraphThicknessInstance) : Prop :=
  ∃ f : Fin i.2.1.length → Fin i.2.2, ∀ c,
    (Cslib.Complexity.Karp.edgeGraph i.1 (edgeClass i f c)).IsPlanar

open Classical in
/-- GRAPH THICKNESS as a decision problem over bitstrings. -/
noncomputable def graphThicknessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphThicknessInstance) x with
  | some i => decide (WellFormed i ∧ GraphThicknessFeasible i)
  | none => false

/-- **GRAPH THICKNESS is NP-complete.** Source: Garey and Johnson (1979), [OPEN3];
Mansfield (1983). -/
public theorem_wanted graphThickness_npComplete :
    graphThicknessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphThicknessDec

end MetaMathlibExt.Complexity.NPComplete.GraphThickness
