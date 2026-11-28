/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF P_4-BIPARTITE GRAPHS: definitions

Source:
M. Barbato and D. Bezzi, "Monopolar graphs: complexity of computing classical graph
parameters", Discrete Applied Mathematics 291 (2021), 277-285, doi:10.1016/j.dam.2020.12.023
(Section 2.1, Proposition 2.8 in the authors' version: "The 3-Colorability problem on monopolar
graphs is NP-complete."; monopolar graphs are `P_4`-bipartite);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class "`P_4`-bipartite" (gc_5),
problem 3-Colourability: NP-complete, recording "NP-complete on monopolar" with the reference to
Barbato and Bezzi (2021).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityP4Bipartite

open GraphColoring (GraphColoringInstance Graph GraphColoringFeasible)

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev ThreeColorabilityP4BipartiteInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH COLORING instance with the same graph and bound `K = 3`. -/
abbrev withThreeColors (i : ThreeColorabilityP4BipartiteInstance) : GraphColoringInstance :=
  (i.1, i.2, 3)

/-- `G` is `P_4`-bipartite: its vertex set splits into a set `A` and the rest `Aᶜ`, each inducing
a graph with no induced path on four vertices. -/
def IsP4Bipartite {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ A : Set (Fin n), ¬ (SimpleGraph.pathGraph 4).IsIndContained (G.induce A) ∧
    ¬ (SimpleGraph.pathGraph 4).IsIndContained (G.induce Aᶜ)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (GRAPH
COLORING's well-formedness), and the graph is `P_4`-bipartite. -/
def WellFormed (i : ThreeColorabilityP4BipartiteInstance) : Prop :=
  GraphColoring.WellFormed (withThreeColors i) ∧ IsP4Bipartite (Graph (withThreeColors i))

/-- The graph is properly 3-colorable. -/
def ThreeColorabilityP4BipartiteFeasible (i : ThreeColorabilityP4BipartiteInstance) : Prop :=
  GraphColoringFeasible (withThreeColors i)

open Classical in
/-- 3-COLORABILITY OF P_4-BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityP4BipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeColorabilityP4BipartiteInstance) x with
  | some i => decide (WellFormed i ∧ ThreeColorabilityP4BipartiteFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityP4Bipartite
