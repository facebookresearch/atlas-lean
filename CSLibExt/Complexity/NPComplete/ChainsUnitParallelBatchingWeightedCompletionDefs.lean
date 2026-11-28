/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|Σw_iC_i`: definitions

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel batching problems"
(`1|chains;p_i=1;p-batch;b<n|Σw_iC_i`, minimal NP-hard in the strong sense,
by reduction from the parallel machine problem);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (`P2|p_i=1;chains|Σw_iC_i`, NP-hard in the strong sense, as
recorded by Brucker and Knust, class "Parallel machine problems without preemption", and by
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 5.3; the full text was
not available to us).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitChainsWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingWeightedCompletion

open MetaMathlibExt.Complexity.NPComplete.TwoProcessorTreePrecedenceCompletionTime
  (TwoProcessorTreePrecedenceCompletionTimeInstance
    TwoProcessorTreePrecedenceCompletionTimeFeasible)

/-- Well-formedness of an instance: with its batch capacity replaced by `2`, it is well formed
for `P2|p_i=1;chains|Σw_iC_i` (unit processing times, the listed pairs name jobs and form a
strict partial order consisting of chains), and the batch capacity satisfies `0 < b < n`. -/
def WellFormed (i : TwoProcessorTreePrecedenceCompletionTimeInstance) : Prop :=
  TwoProcessorUnitChainsWeightedCompletion.WellFormed (2, i.2) ∧ 0 < i.1 ∧
    i.1 < i.2.1.length

open Classical in
/-- `1|chains;p_i=1;p-batch;b<n|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def chainsUnitParallelBatchingWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTreePrecedenceCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTreePrecedenceCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingWeightedCompletion
