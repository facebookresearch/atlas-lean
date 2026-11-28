/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UPGRADING SPANNING TREE: definitions

Source:
S. O. Krumke, M. V. Marathe, H. Noltemeier, R. Ravi, S. S. Ravi, R. Sundaram and H.-C. Wirth,
"Improving minimum cost spanning trees by upgrading nodes", Journal of Algorithms 33 (1999),
92-111, doi:10.1006/jagm.1999.1021 (Definition 2; Section 5, Lemma 18: reduction from MINIMUM
DOMINATING SET);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM UPGRADING SPANNING TREE.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UpgradingSpanningTree

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (an entry
`(u, v, d₀, d₁, d₂)` is the edge `{u, v}` with its three weights), the upgrade costs (entry `v`
is `c(v)`), the bound `D`, and the bound `K`. -/
abbrev UpgradingSpanningTreeInstance := ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ) × List ℕ × ℕ × ℕ

/-- The graph on `Fin n` of a list of edges. -/
def edgesGraph (n : ℕ) (L : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : SimpleGraph (Fin n) :=
  Cslib.Complexity.Karp.edgeGraph n (L.map fun e => (e.1, e.2.1))

/-- The weight `d_W(e)` of the edge `e = (u, v, d₀, d₁, d₂)` after upgrading the vertices in
`W`: `d₂` if both endpoints are in `W`, `d₁` if exactly one is, and `d₀` otherwise. -/
def upgradedWeight (W : Finset ℕ) (e : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ :=
  if e.1 ∈ W ∧ e.2.1 ∈ W then e.2.2.2.2
  else if e.1 ∈ W ∨ e.2.1 ∈ W then e.2.2.2.1 else e.2.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is
connected, every edge has `d₀ ≥ d₁ ≥ d₂`, there is one upgrade cost per vertex, and `0 < K`. -/
def WellFormed (i : UpgradingSpanningTreeInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    (edgesGraph i.1 i.2.1).Connected ∧
    (∀ e ∈ i.2.1, e.2.2.2.2 ≤ e.2.2.2.1 ∧ e.2.2.2.1 ≤ e.2.2.1) ∧
    i.2.2.1.length = i.1 ∧ 0 < i.2.2.2.2

/-- Some set `W` of vertices of upgrade cost at most `K` admits a spanning tree of `G` whose
weight under `d_W` is at most `D`. -/
def UpgradingSpanningTreeFeasible (i : UpgradingSpanningTreeInstance) : Prop :=
  ∃ W : Finset ℕ, W ⊆ Finset.range i.1 ∧ ∑ v ∈ W, i.2.2.1.getD v 0 ≤ i.2.2.2.2 ∧
    ∃ T : List (ℕ × ℕ × ℕ × ℕ × ℕ), T.Sublist i.2.1 ∧ (edgesGraph i.1 T).IsTree ∧
      (T.map (upgradedWeight W)).sum ≤ i.2.2.2.1

open Classical in
/-- UPGRADING SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def upgradingSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UpgradingSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ UpgradingSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UpgradingSpanningTree
