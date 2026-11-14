/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLUSTER DELETION is NP-complete

Source:
R. Shamir, R. Sharan and D. Tsur, "Cluster graph modification problems", Discrete Applied
Mathematics 144(1-2) (2004), 173-182, doi:10.1016/j.dam.2004.01.007 (Theorem 12; NP-completeness
first shown by A. Natanzon, *Complexity and approximation of some graph modification problems*,
Master's thesis, Tel Aviv University, 1999).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClusterDeletion

/-!
# CLUSTER DELETION is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) and a nonnegative integer `K`.
QUESTION: can `G` be made a disjoint union of cliques by deleting at most `K` edges?

Following Shamir, Sharan and Tsur, a graph is a cluster graph if every connected component is
a complete graph (a vertex-disjoint union of cliques), and a Cluster Deletion set for `G` is a
set `F ⊆ E` such that `(V, E \ F)` is a cluster graph. The graph after the deletion is a
`SimpleGraph` `H` on the same vertices with `H ≤ G`; the deleted edges are
`G.edgeSet \ H.edgeSet`. A cluster graph is one in which any two distinct vertices joined by a
walk (Mathlib's `SimpleGraph.Reachable`) are adjacent.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev ClusterDeletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ClusterDeletionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges
in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : ClusterDeletionInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- `H` is a cluster graph: every connected component is complete, i.e. any two distinct
vertices joined by a walk are adjacent. -/
def IsClusterGraph {V : Type*} (H : SimpleGraph V) : Prop :=
  ∀ u v, u ≠ v → H.Reachable u v → H.Adj u v

/-- Deleting at most `K` edges of `G` leaves a cluster graph. -/
def ClusterDeletionFeasible (i : ClusterDeletionInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H ≤ Graph i ∧
    ((Graph i).edgeSet \ H.edgeSet).ncard ≤ i.2.2 ∧ IsClusterGraph H

open Classical in
/-- CLUSTER DELETION as a decision problem over bitstrings. -/
noncomputable def clusterDeletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ClusterDeletionInstance) x with
  | some i => decide (WellFormed i ∧ ClusterDeletionFeasible i)
  | none => false

/-- **CLUSTER DELETION is NP-complete.** Source: Shamir, Sharan and Tsur (2004), Theorem 12;
Natanzon (1999). -/
public theorem_wanted clusterDeletion_npComplete :
    clusterDeletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L clusterDeletionDec

end MetaMathlibExt.Complexity.NPComplete.ClusterDeletion
