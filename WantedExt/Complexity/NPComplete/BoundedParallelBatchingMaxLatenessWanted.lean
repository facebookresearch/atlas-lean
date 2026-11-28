/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED PARALLEL-BATCHING MAXIMUM LATENESS (1|p-batch;b<n|L_max) is NP-complete

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (`1|p-batch;b<n|L_max` strongly
NP-hard, even for `b = 2`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch;b<n|L_max`: minimal NP-hard in the strong sense.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BoundedParallelBatchingMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingMaxLateness

open BoundedParallelBatchingReleaseCompletion
  (BoundedParallelBatchingReleaseCompletionInstance numJobs proc IsBatchSequence completion)

/-!
# BOUNDED PARALLEL-BATCHING MAXIMUM LATENESS (1|p-batch;b<n|L_max) is NP-complete

INSTANCE: a batch capacity `b ∈ ℤ⁺`; jobs `1, …, n` with `b < n`, each with a processing time
`p_j ∈ ℤ⁺` and a due date `d_j ∈ ℤ₀⁺`; and a bound `K ∈ ℤ₀⁺`.
QUESTION: is there a parallel-batching schedule on one machine, with at most `b` jobs in every
batch, whose maximum lateness `max_j (C_j - d_j)` is at most `K`, where `C_j` is the completion
time of job `j`?

Parallel batching is as in `BoundedParallelBatchingReleaseCompletionWanted`
(`1|p-batch;r_i;b<n|ΣC_i`): the jobs are partitioned into batches of at most `b` jobs processed
one after another; all jobs of a batch start together and complete together, and the processing
time of a batch is the largest processing time of its jobs. That module's instance type (the
capacity `b`, one pair per job, the bound `K`), job count `numJobs`, processing times `proc`,
batch sequence `IsBatchSequence` (job `j` in batch `B j`, batch `k` started at `S k`) and job
completion times `completion` are reused; here the second entry of each job's pair is its due
date `d_j` (`dueDate`), and there are no release dates. The maximum lateness is at most `K`
exactly when `C_j ≤ d_j + K` for every job. Due dates and the bound are nonnegative integers: an
instance with integer due dates and bound has the same answer as the one with due dates
`d_j + K` and bound `0` when every `d_j + K` is nonnegative, and is a no-instance otherwise
(every `C_j` is positive). Processing times are positive and `b < n`, as in that module.

Brucker et al. (1998) prove the problem strongly NP-hard, even for `b = 2`; Brucker and Knust
list it as minimal NP-hard in the strong sense. Membership in NP: the batch assignment and the
start times form a certificate, and the earliest start times are at most `∑_j p_j`. Binary
encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BOUNDED PARALLEL-BATCHING MAXIMUM LATENESS (`1|p-batch;b<n|L_max`) is NP-complete.**
Source: Brucker et al. (1998); Brucker and Knust, class bat_p. -/
public theorem_wanted boundedParallelBatchingMaxLateness_npComplete :
    boundedParallelBatchingMaxLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedParallelBatchingMaxLatenessDec

end MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingMaxLateness
