/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SPANNING TREE WITH AT MOST K BRANCH VERTICES: definitions

Source:
L. Gargano, M. Hammar, P. Hell, L. Stacho and U. Vaccaro, "Spanning spiders and
light-splitting switches", Discrete Mathematics 285 (2004), 83-95,
doi:10.1016/j.disc.2004.04.005 (Section 2).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SpanningTreeFewBranchVertices

/-- An instance: the number `n` of vertices, the edge list, and the bound `K`. -/
abbrev SpanningTreeFewBranchVerticesInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : SpanningTreeFewBranchVerticesInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`. -/
def WellFormed (i : SpanningTreeFewBranchVerticesInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

open Classical in
/-- `G` has a spanning tree `T` with at most `K` vertices of degree greater than two in `T`. -/
def SpanningTreeFewBranchVerticesFeasible (i : SpanningTreeFewBranchVerticesInstance) :
    Prop :=
  ∃ T : SimpleGraph (Fin i.1), T ≤ Graph i ∧ T.IsTree ∧
    (Finset.univ.filter fun v => 2 < T.degree v).card ≤ i.2.2

open Classical in
/-- SPANNING TREE WITH AT MOST K BRANCH VERTICES as a decision problem over bitstrings. -/
noncomputable def spanningTreeFewBranchVerticesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SpanningTreeFewBranchVerticesInstance) x with
  | some i => decide (WellFormed i ∧ SpanningTreeFewBranchVerticesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SpanningTreeFewBranchVertices
