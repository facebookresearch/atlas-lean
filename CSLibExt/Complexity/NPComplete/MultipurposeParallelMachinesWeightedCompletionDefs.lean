/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE SCHEDULING (PMPM||Σw_iC_i): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE
WEIGHTED COMPLETION TIME, p. 240 (comment: "NP-complete in the strong sense for m arbitrary
[Lageweg and Lenstra, 1977]", a private communication; the original was not available);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Multipurpose machine problems",
which lists `PMPM||Σw_iC_i` as minimal NP-hard (strongly), crediting an unpublished result of
J. K. Lenstra.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelMachinesMakespanDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesWeightedCompletion

open MultipurposeParallelTwoMachinesWeightedCompletion
  (MultipurposeParallelTwoMachinesWeightedCompletionInstance
    MultipurposeParallelTwoMachinesWeightedCompletionFeasible)

/-- Well-formedness of an instance: a well-formed `PMPM||C_max` instance (`m ≥ 1`, nonempty
machine sets in `{1, …, m}`, single-operation jobs) and one weight per job. -/
def WellFormed (i : MultipurposeParallelTwoMachinesWeightedCompletionInstance) : Prop :=
  MultipurposeParallelMachinesMakespan.WellFormed i.1 ∧ i.2.length = i.1.2.1.length

open Classical in
/-- `PMPM||Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelMachinesWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesWeightedCompletionInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultipurposeParallelTwoMachinesWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesWeightedCompletion
