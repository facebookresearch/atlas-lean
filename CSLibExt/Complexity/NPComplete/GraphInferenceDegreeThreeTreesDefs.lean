/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH INFERENCE FROM A WALK FOR TREES OF DEGREE AT MOST 3: definitions

Source:
O. Maruyama and S. Miyano, "Graph inference from a walk for trees of bounded degree 3 is
NP-complete", in *Mathematical Foundations of Computer Science 1995*, Lecture Notes in Computer
Science 969, Springer (1995), 257-266, doi:10.1007/3-540-60246-1_132 (Theorem 1; full version:
RIFIS Technical Report 94, Kyushu University (1994), https://hdl.handle.net/2324/3076);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM GRAPH INFERENCE.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphInferenceDegreeThreeTrees

/-- An instance: the string `x` of colors and the bound `K` on the number of edges. -/
abbrev GraphInferenceInstance := List ℕ × ℕ

/-- Well-formedness of an instance: `K` is positive. -/
def WellFormed (i : GraphInferenceInstance) : Prop :=
  0 < i.2

open Classical in
/-- Some tree of bounded degree 3 with at most `K` edges, with an edge-coloring, has a walk that
traverses every edge and whose trace is `x`. -/
def GraphInferenceFeasible (i : GraphInferenceInstance) : Prop :=
  ∃ m : ℕ, ∃ G : SimpleGraph (Fin m), ∃ c : Sym2 (Fin m) → ℕ,
    G.IsTree ∧ (∀ v, G.degree v ≤ 3) ∧ G.edgeSet.ncard ≤ i.2 ∧
      ∃ u v : Fin m, ∃ w : G.Walk u v, (∀ e ∈ G.edgeSet, e ∈ w.edges) ∧ w.edges.map c = i.1

open Classical in
/-- GRAPH INFERENCE FROM A WALK FOR TREES OF DEGREE AT MOST 3 as a decision problem over
bitstrings. -/
noncomputable def graphInferenceDegreeThreeTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphInferenceInstance) x with
  | some i => decide (WellFormed i ∧ GraphInferenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphInferenceDegreeThreeTrees
