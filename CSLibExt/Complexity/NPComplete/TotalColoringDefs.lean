/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL COLORING: definitions

Source:
A. Sánchez-Arroyo, "Determining the total colouring number is NP-hard", Discrete Mathematics
78 (1989), 315-319, doi:10.1016/0012-365X(89)90187-8;
C. J. H. McDiarmid and A. Sánchez-Arroyo, "Total colouring regular bipartite graphs is
NP-hard", Discrete Mathematics 124 (1994), 155-162, doi:10.1016/0012-365X(92)00058-Y.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalColoring

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, number of colors `K`. -/
abbrev TotalColoringInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TotalColoringInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : TotalColoringInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- A total coloring with `K` colors: a proper vertex coloring `cv` and a proper edge coloring
`ce` (a coloring of the line graph) such that every edge `e` and every endpoint `v ∈ e` get
distinct colors. -/
def TotalColoringFeasible (i : TotalColoringInstance) : Prop :=
  ∃ (cv : (Graph i).Coloring (Fin i.2.2)) (ce : (Graph i).lineGraph.Coloring (Fin i.2.2)),
    ∀ e : (Graph i).edgeSet, ∀ v ∈ (e : Sym2 (Fin i.1)), ce e ≠ cv v

open Classical in
/-- TOTAL COLORING as a decision problem over bitstrings. -/
noncomputable def totalColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := TotalColoringInstance) x with
  | some i => decide (WellFormed i ∧ TotalColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TotalColoring
