/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COVERING BY CLIQUES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT17] COVERING BY
CLIQUES;
L. T. Kou, L. J. Stockmeyer, and C. K. Wong, "Covering edges by cliques with
regard to keyword conflicts and intersection graphs", Communications of the ACM
21 (1978), 135-139, doi:10.1145/359340.359346;
J. Orlin, "Contentment in graph theory: covering graphs with cliques",
Indagationes Mathematicae (Proceedings) 80 (1977), 406-424,
doi:10.1016/1385-7258(77)90055-5.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoveringByCliques

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev CoveringByCliquesInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CoveringByCliquesInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |E|`, the length of the edge list. -/
def WellFormed (i : CoveringByCliquesInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- The edges are covered by at most `K` cliques: for some `k ≤ K` there are vertex sets
`S j`, `j : Fin k`, each a clique of the graph, such that every edge has both endpoints in some
`S j`. -/
def CoveringByCliquesFeasible (i : CoveringByCliquesInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ S : Fin k → Set (Fin i.1),
    (∀ j, (Graph i).IsClique (S j)) ∧
      ∀ u v, (Graph i).Adj u v → ∃ j, u ∈ S j ∧ v ∈ S j

open Classical in
/-- COVERING BY CLIQUES as a decision problem over bitstrings. -/
noncomputable def coveringByCliquesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoveringByCliquesInstance) x with
  | some i => decide (WellFormed i ∧ CoveringByCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CoveringByCliques
