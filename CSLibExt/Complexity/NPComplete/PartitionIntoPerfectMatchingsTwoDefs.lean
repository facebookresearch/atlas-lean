/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO PERFECT MATCHINGS with K = 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT16] PARTITION INTO PERFECT MATCHINGS,
comment: remains NP-complete for `K = 2`;
T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the 10th Annual ACM
Symposium on Theory of Computing (STOC 1978), 216-226, doi:10.1145/800133.804350;
E. D. Demaine, K. Karntikoon and N. Pitimanaaree, "2-Colorable perfect matching is NP-complete in
2-connected 3-regular planar graphs", Theory of Computing Systems 69 (2025),
doi:10.1007/s00224-025-10221-2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartitionIntoPerfectMatchingsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchingsTwo

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchings
  (PartitionIntoPerfectMatchingsInstance PartitionIntoPerfectMatchingsFeasible)

/-- Well-formedness of an instance: a well-formed PARTITION INTO PERFECT MATCHINGS instance
(simple edge list, `0 < K ≤ |V|`) whose bound is `K = 2`. -/
def WellFormed (i : PartitionIntoPerfectMatchingsInstance) : Prop :=
  PartitionIntoPerfectMatchings.WellFormed i ∧ i.2.2 = 2

open Classical in
/-- PARTITION INTO PERFECT MATCHINGS with `K = 2` as a decision problem over bitstrings. -/
noncomputable def partitionIntoPerfectMatchingsTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoPerfectMatchingsInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoPerfectMatchingsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchingsTwo
