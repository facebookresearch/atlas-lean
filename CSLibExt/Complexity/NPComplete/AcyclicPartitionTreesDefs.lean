/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACYCLIC PARTITION for trees: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND15] ACYCLIC PARTITION, comment;
the pseudo-polynomial algorithm cited there: J. A. Lukes, "Efficient algorithm for the
partitioning of trees", IBM Journal of Research and Development 18 (1974), 217-224,
doi:10.1147/rd.183.0217.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import CSLibExt.Complexity.NPComplete.AcyclicPartitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AcyclicPartitionTrees

/-- The underlying undirected graph of the instance on `Fin n`: an edge `{u, v}` for each arc
`(u, v)`. -/
def underlyingGraph (i : AcyclicPartition.AcyclicPartitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.2.1.map fun a => (a.1, a.2.1))

/-- Well-formedness of an instance: ACYCLIC PARTITION well-formedness, no two arcs in opposite
directions between the same two vertices, and the underlying undirected graph is a tree. -/
def WellFormed (i : AcyclicPartition.AcyclicPartitionInstance) : Prop :=
  AcyclicPartition.WellFormed i ∧
    (∀ a ∈ i.2.2.1, (a.2.1, a.1) ∉ i.2.2.1.map fun a => (a.1, a.2.1)) ∧
    (underlyingGraph i).IsTree

open Classical in
/-- ACYCLIC PARTITION for trees as a decision problem over bitstrings. -/
noncomputable def acyclicPartitionTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AcyclicPartition.AcyclicPartitionInstance) x with
  | some i => decide (WellFormed i ∧ AcyclicPartition.AcyclicPartitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.AcyclicPartitionTrees
