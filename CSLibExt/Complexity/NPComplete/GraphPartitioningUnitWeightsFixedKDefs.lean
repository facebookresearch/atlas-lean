/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH PARTITIONING with unit weights and fixed `K ≥ 3`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND14] GRAPH PARTITIONING, p. 209, comment:
"Remains NP-complete for fixed K ≥ 3 even if all vertex and edge weights are 1" (the entry's
reference is [Hyafil and Rivest, 1973], transformation from PARTITION INTO TRIANGLES);
L. Hyafil and R. L. Rivest, "Graph partitioning and constructing optimal decision trees are
polynomial complete problems", IRIA-Laboria Rapport 33 (1973).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphPartitioningDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphPartitioningUnitWeightsFixedK

open MetaMathlibExt.Complexity.NPComplete.GraphPartitioning
  (GraphPartitioningInstance GraphPartitioningFeasible)

/-- An instance for a fixed block bound `K`: vertex count `n` (vertices `0, …, n - 1`), the
vertex weights `[w 0, …, w (n - 1)]`, the edges `(u, v, l(e))`, and the bound `J`. -/
abbrev FixedBoundInstance := ℕ × List ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The GRAPH PARTITIONING instance given by `i` and the block bound `K`. -/
abbrev withBound (i : FixedBoundInstance) (K : ℕ) : GraphPartitioningInstance :=
  (i.1, i.2.1, i.2.2.1, K, i.2.2.2)

/-- Well-formedness of an instance for the bound `K`: the GRAPH PARTITIONING instance
`withBound i K` is well-formed, every vertex weight is `1`, and every edge length is `1`. -/
def WellFormed (K : ℕ) (i : FixedBoundInstance) : Prop :=
  GraphPartitioning.WellFormed (withBound i K) ∧ (∀ x ∈ i.2.1, x = 1) ∧
    ∀ e ∈ i.2.2.1, e.2.2 = 1

open Classical in
/-- GRAPH PARTITIONING with unit weights and the block bound fixed to `K`, as a decision problem
over bitstrings. -/
noncomputable def graphPartitioningUnitWeightsDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedBoundInstance) x with
  | some i => decide (WellFormed K i ∧ GraphPartitioningFeasible (withBound i K))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphPartitioningUnitWeightsFixedK
