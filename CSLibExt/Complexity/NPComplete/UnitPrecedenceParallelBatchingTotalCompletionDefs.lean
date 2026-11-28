/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|prec;p_i=1;p-batch;b<n|ΣC_i`: definitions

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel batching problems"
(`1|prec;p_i=1;p-batch;b<n|ΣC_i`, minimal NP-hard in the strong sense,
by reduction from the parallel machine problem `P|prec;p_i=1|ΣC_i`);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22
(`P|prec;p_i=1|ΣC_i` strongly NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingTotalCompletionDefs
public import CSLibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance)
open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingTotalCompletion
  (PrecedenceConstrainedSchedulingTotalCompletionFeasible)
open MetaMathlibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingMakespan (WellFormed)

open Classical in
/-- `1|prec;p_i=1;p-batch;b<n|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def unitPrecedenceParallelBatchingTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceConstrainedSchedulingTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingTotalCompletion
