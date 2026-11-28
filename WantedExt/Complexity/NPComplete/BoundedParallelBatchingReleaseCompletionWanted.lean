/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED PARALLEL-BATCHING TOTAL COMPLETION TIME WITH RELEASE DATES (1|p-batch;r_i;b<n|ΣC_i)
is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch;r_i;b<n|ΣC_i`: minimal NP-hard in the strong sense, by reduction from
the single machine problem `1|r_i|ΣC_i`; J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker,
"Complexity of machine scheduling problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X (`1|r_j|ΣC_j` strongly NP-hard); parallel-batching model from
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseCompletion

/-!
# BOUNDED PARALLEL-BATCHING TOTAL COMPLETION TIME WITH RELEASE DATES (1|p-batch;r_i;b<n|ΣC_i)
is NP-complete

INSTANCE: a batch capacity `b ∈ ℤ⁺`; jobs `1, …, n` with `b < n`, each with a processing time
`p_j ∈ ℤ⁺` and a release date `r_j ∈ ℤ₀⁺`; and a bound `K ∈ ℤ⁺`.
QUESTION: is there a parallel-batching schedule on one machine, with at most `b` jobs in every
batch and no job started before its release date, whose total completion time `∑_j C_j` is at
most `K`, where `C_j` is the completion time of job `j`?

Parallel batching (Brucker et al. 1998; Brucker and Knust's class `p-batch`): the machine
processes up to `b` jobs simultaneously; the jobs are partitioned into batches processed one
after another; all jobs of a batch start together and complete together, and the processing
time of a batch is the largest processing time of its jobs. A schedule puts job `j` into batch
`B j` and starts batch `k` at time `S k`: batch `k` occupies `[S k, S k + P k)`, where `P k`
(`batchLength`) is the largest processing time of its jobs, and a batch with a larger index
starts only after every nonempty batch with a smaller index has completed. Empty batch indices
play no role. Job `j` starts at `S (B j)` and completes at `C_j = S (B j) + P (B j)`. Start times
are natural numbers: for a fixed sequence of batches the earliest start times are integral and
no later than any others, and every `C_j` is nondecreasing in the start times. The bounded model
`b < n` is part of the instance class. Processing times and the bound are positive, as in the
classical problem `1|r_j|ΣC_j` whose NP-hardness the Brucker-Knust entry cites (the repository's
`TotalCompletionTimeWithReleaseTimesWanted` states it with the same conditions).

Brucker and Knust list this problem as minimal NP-hard in the strong sense, by reduction from
the single machine problem `1|r_i|ΣC_i`: with `b = 1` every batch holds one job, so the
instances with `b = 1` and `n ≥ 2` are those of `1|r_j|ΣC_j` with at least two jobs
(`TotalCompletionTimeWithReleaseTimesWanted`), strongly NP-hard by Lenstra, Rinnooy Kan and
Brucker (1977), Theorem 4(a). Membership in NP: the batch assignment and the start times form a
certificate, and the earliest start times are at most `max_j r_j + ∑_j p_j`. The jobs are
`Fin n`, one per listed pair `(p_j, r_j)`. Binary encoding of all numbers (the problem is
NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BOUNDED PARALLEL-BATCHING TOTAL COMPLETION TIME WITH RELEASE DATES
(`1|p-batch;r_i;b<n|ΣC_i`) is NP-complete.** Source: Brucker and Knust, class bat_p; Lenstra,
Rinnooy Kan and Brucker (1977). -/
public theorem_wanted boundedParallelBatchingReleaseCompletion_npComplete :
    boundedParallelBatchingReleaseCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedParallelBatchingReleaseCompletionDec

end MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseCompletion
