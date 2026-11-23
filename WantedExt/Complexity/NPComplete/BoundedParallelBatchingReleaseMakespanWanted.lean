/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED PARALLEL-BATCHING MAKESPAN WITH RELEASE DATES (1|p-batch;r_i;b<n|C_max) is NP-complete

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (`1|p-batch;r_j;b<n|C_max`
strongly NP-hard, even for `b = 2`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch;r_i;b<n|C_max`: minimal NP-hard in the strong sense.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BoundedParallelBatchingReleaseCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseMakespan

open BoundedParallelBatchingReleaseCompletion
  (BoundedParallelBatchingReleaseCompletionInstance numJobs proc release IsBatchSequence
    completion WellFormed)

/-!
# BOUNDED PARALLEL-BATCHING MAKESPAN WITH RELEASE DATES (1|p-batch;r_i;b<n|C_max) is NP-complete

INSTANCE: a batch capacity `b ∈ ℤ⁺`; jobs `1, …, n` with `b < n`, each with a processing time
`p_j ∈ ℤ⁺` and a release date `r_j ∈ ℤ₀⁺`; and a bound `K ∈ ℤ⁺`.
QUESTION: is there a parallel-batching schedule on one machine, with at most `b` jobs in every
batch and no job started before its release date, whose makespan `max_j C_j` is at most `K`,
where `C_j` is the completion time of job `j`?

The instance, its well-formedness (`0 < b < n`, positive processing times, positive `K`) and the
parallel-batching schedule are those of `BoundedParallelBatchingReleaseCompletionWanted`
(`1|p-batch;r_i;b<n|ΣC_i`), reused unchanged: the jobs are partitioned into batches of at most
`b` jobs processed one after another, all jobs of a batch start together and complete together,
the processing time of a batch is the largest processing time of its jobs, job `j` is in batch
`B j`, batch `k` starts at `S k` (`IsBatchSequence`), and `completion` gives `C_j`. Only the
objective differs.

Brucker et al. (1998) prove the problem strongly NP-hard, even for `b = 2`; Brucker and Knust
list it as minimal NP-hard in the strong sense. Membership in NP: the batch assignment and the
start times form a certificate, and the earliest start times are at most `max_j r_j + ∑_j p_j`.
Binary encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **BOUNDED PARALLEL-BATCHING MAKESPAN WITH RELEASE DATES (`1|p-batch;r_i;b<n|C_max`) is
NP-complete.** Source: Brucker et al. (1998); Brucker and Knust, class bat_p. -/
public theorem_wanted boundedParallelBatchingReleaseMakespan_npComplete :
    boundedParallelBatchingReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedParallelBatchingReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseMakespan
