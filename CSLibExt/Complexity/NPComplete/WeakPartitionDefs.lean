/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEAK PARTITION: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982),
182-195, doi:10.1016/0196-6774(82)90018-9, problem [9] WEAK PARTITION (reference: Shamir,
independently rediscovered by van Emde Boas and by Rubin; transformation from PARTITION);
A. Shamir, "On the cryptocomplexity of knapsack systems", Proc. 11th Annual ACM Symposium on
Theory of Computing (1979), 118-129, doi:10.1145/800135.804405;
P. van Emde Boas, "Another NP-complete partition problem and the complexity of computing short
vectors in a lattice", Report 81-04, Department of Mathematics, University of Amsterdam (1981).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Partition
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeakPartition

open MetaMathlibExt.Complexity.NPComplete.Partition (PartitionInstance)

/-- Well-formedness of an instance: every size is positive. -/
def WellFormed (i : PartitionInstance) : Prop :=
  ∀ a ∈ i, 0 < a

/-- Some two disjoint non-empty sets `A₁`, `A₂` of elements have the same total size. -/
def WeakPartitionFeasible (i : PartitionInstance) : Prop :=
  ∃ A₁ A₂ : Finset (Fin i.length), Disjoint A₁ A₂ ∧ A₁.Nonempty ∧ A₂.Nonempty ∧
    ∑ a ∈ A₁, i.get a = ∑ a ∈ A₂, i.get a

open Classical in
/-- WEAK PARTITION as a decision problem over bitstrings. -/
noncomputable def weakPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionInstance) x with
  | some i => decide (WellFormed i ∧ WeakPartitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeakPartition
