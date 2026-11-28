/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED PARALLEL-BATCHING MAXIMUM LATENESS (1|p-batch;b<n|L_max): definitions

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (`1|p-batch;b<n|L_max` strongly
NP-hard, even for `b = 2`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch;b<n|L_max`: minimal NP-hard in the strong sense.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingMaxLateness

open BoundedParallelBatchingReleaseCompletion
  (BoundedParallelBatchingReleaseCompletionInstance numJobs proc IsBatchSequence completion)

/-- The due date `d_j` of job `j`: the second entry of its pair. -/
def dueDate (i : BoundedParallelBatchingReleaseCompletionInstance) (j : Fin (numJobs i)) : ℕ :=
  (i.2.1.get j).2

/-- Well-formedness of an instance: the batch capacity `b` is positive and less than the number
`n` of jobs, and every processing time is positive. -/
def WellFormed (i : BoundedParallelBatchingReleaseCompletionInstance) : Prop :=
  0 < i.1 ∧ i.1 < numJobs i ∧ ∀ job ∈ i.2.1, 0 < job.1

/-- Some parallel-batching schedule has at most `b` jobs in every batch and completes every job
`j` by `d_j + K`, i.e. has maximum lateness at most `K`. -/
def BoundedParallelBatchingMaxLatenessFeasible
    (i : BoundedParallelBatchingReleaseCompletionInstance) : Prop :=
  ∃ (B : Fin (numJobs i) → ℕ) (S : ℕ → ℕ), IsBatchSequence (proc i) B S ∧
    (∀ k, (Finset.univ.filter (fun j => B j = k)).card ≤ i.1) ∧
    ∀ j, completion (proc i) B S j ≤ dueDate i j + i.2.2

open Classical in
/-- BOUNDED PARALLEL-BATCHING MAXIMUM LATENESS as a decision problem over bitstrings. -/
noncomputable def boundedParallelBatchingMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedParallelBatchingReleaseCompletionInstance) x with
  | some i => decide (WellFormed i ∧ BoundedParallelBatchingMaxLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingMaxLateness
