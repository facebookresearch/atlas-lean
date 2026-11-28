/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BALANCED CONNECTED PARTITION: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MAXIMUM BALANCED CONNECTED PARTITION;
J. Chlebíková, "Approximating the maximally balanced connected partition problem in graphs",
Information Processing Letters 60(5) (1996), 225-230, doi:10.1016/S0020-0190(96)00175-5
(NP-hard even for bipartite graphs with unit weights);
M. E. Dyer and A. M. Frieze, "On the complexity of partitioning graphs into connected
subgraphs", Discrete Applied Mathematics 10 (1985), 139-153,
doi:10.1016/0166-218X(85)90008-3 (Theorem 2.2 with `k = 2`: deciding whether a bipartite
graph on `n` vertices splits into two connected induced subgraphs of `n / 2` vertices each is
NP-complete).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BalancedConnectedPartition

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, vertex weights
`[w 0, ..., w (n - 1)]`, and the bound `K`. -/
abbrev BalancedConnectedPartitionInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BalancedConnectedPartitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The weight `w(v)` of a vertex. -/
def weight (i : BalancedConnectedPartitionInstance) (v : Fin i.1) : ℕ :=
  i.2.2.1.getD v 0

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is
connected, there is one weight per vertex, and `0 < K`. -/
def WellFormed (i : BalancedConnectedPartitionInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).Connected ∧ i.2.2.1.length = i.1 ∧ 0 < i.2.2.2

/-- Some set `S` of vertices gives a partition `(S, V \ S)` into nonempty sets that both induce
connected subgraphs, with `min {w(S), w(V \ S)} ≥ K`. -/
def BalancedConnectedPartitionFeasible (i : BalancedConnectedPartitionInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.Nonempty ∧ Sᶜ.Nonempty ∧
    ((Graph i).induce (S : Set (Fin i.1))).Connected ∧
    ((Graph i).induce ((Sᶜ : Finset (Fin i.1)) : Set (Fin i.1))).Connected ∧
    i.2.2.2 ≤ min (∑ v ∈ S, weight i v) (∑ v ∈ Sᶜ, weight i v)

open Classical in
/-- BALANCED CONNECTED PARTITION as a decision problem over bitstrings. -/
noncomputable def balancedConnectedPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BalancedConnectedPartitionInstance) x with
  | some i => decide (WellFormed i ∧ BalancedConnectedPartitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BalancedConnectedPartition
