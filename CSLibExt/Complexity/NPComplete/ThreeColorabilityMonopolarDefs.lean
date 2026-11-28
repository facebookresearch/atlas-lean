/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF MONOPOLAR GRAPHS: definitions

Source:
M. Barbato and D. Bezzi, "Monopolar graphs: complexity of computing classical graph
parameters", Discrete Applied Mathematics 291 (2021), 277-285, doi:10.1016/j.dam.2020.12.023
(Section 2.1, Proposition 2.8 in the authors' version: "The 3-Colorability problem on monopolar
graphs is NP-complete.");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class "monopolar" (gc_1272),
problem 3-Colourability: NP-complete, with the reference to Barbato and Bezzi (2021).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ClusterDeletionDefs
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityMonopolar

open GraphColoring (GraphColoringInstance Graph GraphColoringFeasible)

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev ThreeColorabilityMonopolarInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH COLORING instance with the same graph and bound `K = 3`. -/
abbrev withThreeColors (i : ThreeColorabilityMonopolarInstance) : GraphColoringInstance :=
  (i.1, i.2, 3)

/-- `G` is monopolar: its vertex set splits into a stable set `A` and the rest `Aᶜ`, which induces a
union of vertex-disjoint cliques (a cluster graph). -/
def IsMonopolar {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ A : Set (Fin n), G.IsIndepSet A ∧ ClusterDeletion.IsClusterGraph (G.induce Aᶜ)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (GRAPH
COLORING's well-formedness), and the graph is monopolar. -/
def WellFormed (i : ThreeColorabilityMonopolarInstance) : Prop :=
  GraphColoring.WellFormed (withThreeColors i) ∧ IsMonopolar (Graph (withThreeColors i))

/-- The graph is properly 3-colorable. -/
def ThreeColorabilityMonopolarFeasible (i : ThreeColorabilityMonopolarInstance) : Prop :=
  GraphColoringFeasible (withThreeColors i)

open Classical in
/-- 3-COLORABILITY OF MONOPOLAR GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityMonopolarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeColorabilityMonopolarInstance) x with
  | some i => decide (WellFormed i ∧ ThreeColorabilityMonopolarFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityMonopolar
