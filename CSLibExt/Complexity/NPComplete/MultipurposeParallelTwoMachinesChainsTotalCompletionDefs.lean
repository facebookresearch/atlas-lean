/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS (PMPM2|chains|ΣC_i): definitions

Source:
J. Du, J. Y.-T. Leung and G. H. Young, "Scheduling chain-structured tasks to minimize makespan
and mean flow time", Information and Computation 92 (1991), 219-236,
doi:10.1016/0890-5401(91)90009-Q;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Multipurpose
machine problems" (`PMPM2|chains|ΣC_i`, minimal NP-hard in the strong sense, credited to Du et
al. (1991)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelPrecedenceTotalCompletionDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsTotalCompletion

open MultipurposeParallelTwoMachinesChainsMakespan
  (MultipurposeParallelTwoMachinesChainsMakespanInstance WellFormed)
open MultipurposeParallelPrecedenceTotalCompletion
  (MultipurposeParallelPrecedenceTotalCompletionFeasible)

open Classical in
/-- `PMPM2|chains|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesChainsTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesChainsMakespanInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultipurposeParallelPrecedenceTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesChainsTotalCompletion
