/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED PARALLEL-BATCHING MAKESPAN WITH RELEASE DATES (1|p-batch;r_i;b<n|C_max): definitions

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (`1|p-batch;r_j;b<n|C_max`
strongly NP-hard, even for `b = 2`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch;r_i;b<n|C_max`: minimal NP-hard in the strong sense.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseMakespan

open BoundedParallelBatchingReleaseCompletion
  (BoundedParallelBatchingReleaseCompletionInstance numJobs proc release IsBatchSequence
    completion WellFormed)

/-- Some parallel-batching schedule has at most `b` jobs in every batch, starts every job (at the
start `S (B j)` of its batch) no earlier than its release date, and completes every job by
`K`. -/
def BoundedParallelBatchingReleaseMakespanFeasible
    (i : BoundedParallelBatchingReleaseCompletionInstance) : Prop :=
  ∃ (B : Fin (numJobs i) → ℕ) (S : ℕ → ℕ), IsBatchSequence (proc i) B S ∧
    (∀ k, (Finset.univ.filter (fun j => B j = k)).card ≤ i.1) ∧
    (∀ j, release i j ≤ S (B j)) ∧ ∀ j, completion (proc i) B S j ≤ i.2.2

open Classical in
/-- BOUNDED PARALLEL-BATCHING MAKESPAN WITH RELEASE DATES as a decision problem over
bitstrings. -/
noncomputable def boundedParallelBatchingReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedParallelBatchingReleaseCompletionInstance) x with
  | some i => decide (WellFormed i ∧ BoundedParallelBatchingReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseMakespan
