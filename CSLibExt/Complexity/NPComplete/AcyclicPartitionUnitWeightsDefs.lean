/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACYCLIC PARTITION with unit weights and costs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND15] ACYCLIC PARTITION, p. 209, comment:
"Remains NP-complete even if all v ∈ V have w(v) = 1 and all a ∈ A have c(a) = 1" (the
entry's reference is [Garey and Johnson, ——], unpublished; transformation from X3C).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.AcyclicPartitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AcyclicPartitionUnitWeights

open MetaMathlibExt.Complexity.NPComplete.AcyclicPartition
  (AcyclicPartitionInstance AcyclicPartitionFeasible)

/-- Well-formedness of an instance: a well-formed ACYCLIC PARTITION instance in which every
vertex weight and every arc cost is `1`. -/
def WellFormed (i : AcyclicPartitionInstance) : Prop :=
  AcyclicPartition.WellFormed i ∧ (∀ x ∈ i.2.1, x = 1) ∧ ∀ a ∈ i.2.2.1, a.2.2 = 1

open Classical in
/-- ACYCLIC PARTITION with unit weights and costs as a decision problem over bitstrings. -/
noncomputable def acyclicPartitionUnitWeightsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := AcyclicPartitionInstance) x with
  | some i => decide (WellFormed i ∧ AcyclicPartitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.AcyclicPartitionUnitWeights
