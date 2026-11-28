/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED DOMINATING SET ON SPLIT GRAPHS: definitions

Source:
K. White, M. Farber and W. Pulleyblank, "Steiner trees, connected domination and strongly
chordal graphs", Networks 15 (1985), 109-124, doi:10.1002/net.3230150109;
A. Mohanapriya, P. Renjith and N. Sadagopan, "On convexity in split graphs: complexity of
Steiner tree and domination", Journal of Combinatorial Optimization 47 (2024), no. 2,
article 8, doi:10.1007/s10878-024-01105-1 (arXiv:2210.02288, Section 3, "Application 4:
Domination and its variants").
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Domination

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SplitConnectedDominatingSet

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev SplitConnectedDominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : SplitConnectedDominatingSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is a split
graph (some vertex set `C` is a clique and its complement is an independent set), and `0 < K`. -/
def WellFormed (i : SplitConnectedDominatingSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∃ C : Set (Fin i.1), (Graph i).IsClique C ∧ (Graph i).IsIndepSet Cᶜ) ∧
    0 < i.2.2

/-- Some dominating set `V'` of at most `K` vertices induces a connected subgraph. -/
def SplitConnectedDominatingSetFeasible (i : SplitConnectedDominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧ (Graph i).IsDominating (↑S : Set (Fin i.1)) ∧
    ((Graph i).induce (↑S : Set (Fin i.1))).Connected

open Classical in
/-- CONNECTED DOMINATING SET ON SPLIT GRAPHS as a decision problem over bitstrings. -/
noncomputable def splitConnectedDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SplitConnectedDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ SplitConnectedDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SplitConnectedDominatingSet
