/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HIERARCHICAL CLUSTERING with Dasgupta's cost: definitions

Source:
S. Dasgupta, "A cost function for similarity-based hierarchical clustering", Proceedings of the
48th Annual ACM Symposium on Theory of Computing (STOC 2016), 118-127,
doi:10.1145/2897518.2897527 (arXiv:1510.05043), Section 2 (the cost function) and Section 4
(NP-hardness of finding a tree of minimum cost).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Bioinformatics.Clustering.OptimalLeafOrdering

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DasguptaHierarchicalClustering

open Cslib.Bioinformatics.Clustering.OptimalLeafOrdering

/-- An instance: the number of vertices `n` (vertices `0, …, n - 1`), the weighted edges
`(i, j, w_{ij})`, and the bound `K`. -/
abbrev DasguptaHierarchicalClusteringInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- `|leaves(T[i ∨ j])|`: descending from the root into a child (left child first) as long as
that child's leaves contain both `i` and `j`, the number of leaves of the subtree where descent
stops (`1` at a leaf, and `T.leaves.length` when no proper child subtree contains both; if the
leaf labels of `T` are distinct and both `i` and `j` occur among them, the number of leaves of
the smallest rooted subtree containing both). -/
def lcaLeafCount : Dendrogram ℕ → ℕ → ℕ → ℕ
  | .leaf _, _, _ => 1
  | .node l r, i, j =>
    if i ∈ l.leaves ∧ j ∈ l.leaves then lcaLeafCount l i j
    else if i ∈ r.leaves ∧ j ∈ r.leaves then lcaLeafCount r i j
    else (Dendrogram.node l r).leaves.length

/-- Dasgupta's cost `∑_{{i, j} ∈ E} w_{ij} · |leaves(T[i ∨ j])|` of the tree `T`. -/
def cost (i : DasguptaHierarchicalClusteringInstance) (T : Dendrogram ℕ) : ℕ :=
  (i.2.1.map fun e => e.2.2 * lcaLeafCount T e.1 e.2.1).sum

/-- Well-formedness of an instance: there is at least one vertex, the edges are listed once
each (no repeated pair in either orientation), join two distinct vertices, and have positive
weights. -/
def WellFormed (i : DasguptaHierarchicalClusteringInstance) : Prop :=
  0 < i.1 ∧ (i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ 0 < e.2.2 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)

/-- Some rooted binary tree whose leaves are exactly the vertices, each once, has cost at
most `K`. -/
def DasguptaHierarchicalClusteringFeasible (i : DasguptaHierarchicalClusteringInstance) :
    Prop :=
  ∃ T : Dendrogram ℕ, T.leaves.Perm (List.range i.1) ∧ cost i T ≤ i.2.2

open Classical in
/-- HIERARCHICAL CLUSTERING with Dasgupta's cost as a decision problem over bitstrings. -/
noncomputable def dasguptaHierarchicalClusteringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DasguptaHierarchicalClusteringInstance) x with
  | some i => decide (WellFormed i ∧ DasguptaHierarchicalClusteringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DasguptaHierarchicalClustering
