/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH THICKNESS: definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphThickness

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

end MetaMathlibExt.Complexity.NPComplete.GraphThickness
