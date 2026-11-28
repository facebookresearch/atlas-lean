/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH PARTITIONING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND14] GRAPH
PARTITIONING;
L. Hyafil and R. L. Rivest, "Graph partitioning and constructing optimal
decision trees are polynomial complete problems", Rapport de Recherche 33,
IRIA-Laboria, Rocquencourt (1973).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphPartitioning

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), vertex weights `w(0), ...,
w(n - 1)`, edge list with lengths `(u, v, l({u, v}))`, `K`, `J`. -/
abbrev GraphPartitioningInstance := ℕ × List ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: one positive weight per vertex, the edge list describes a
simple graph on `{0, ..., n - 1}` (no self-loops, no edge listed twice in either orientation)
with positive lengths, and `0 < K`, `0 < J`. -/
def WellFormed (i : GraphPartitioningInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ x ∈ i.2.1, 0 < x) ∧
    (i.2.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ 0 < e.2.2 ∧
      (e.2.1, e.1) ∉ i.2.2.1.map fun e => (e.1, e.2.1)) ∧
    0 < i.2.2.2.1 ∧ 0 < i.2.2.2.2

/-- A partition into blocks (the fibres of a labelling `c`) in which every block has total
vertex weight at most `K`, and the edges whose endpoints lie in different blocks have total
length at most `J`. -/
def GraphPartitioningFeasible (i : GraphPartitioningInstance) : Prop :=
  ∃ c : ℕ → ℕ,
    (∀ b, ∑ v ∈ (Finset.range i.1).filter (fun v => c v = b), i.2.1.getD v 0 ≤
      i.2.2.2.1) ∧
    ((i.2.2.1.filter fun e => decide (c e.1 ≠ c e.2.1)).map fun e => e.2.2).sum ≤ i.2.2.2.2

open Classical in
/-- GRAPH PARTITIONING as a decision problem over bitstrings. -/
noncomputable def graphPartitioningDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphPartitioningInstance) x with
  | some i => decide (WellFormed i ∧ GraphPartitioningFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphPartitioning
