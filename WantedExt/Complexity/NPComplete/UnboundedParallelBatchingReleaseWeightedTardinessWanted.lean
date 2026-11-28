/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNBOUNDED PARALLEL-BATCHING WEIGHTED TARDINESS WITH RELEASE DATES (1|p-batch;r_i|Σw_iT_i)
is NP-complete

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (`1|p-batch|Σw_jT_j` NP-hard);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch;r_i|Σw_iT_i`.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnboundedParallelBatchingReleaseWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingReleaseWeightedTardiness

open BoundedParallelBatchingReleaseCompletion (IsBatchSequence completion)

/-!
# UNBOUNDED PARALLEL-BATCHING WEIGHTED TARDINESS WITH RELEASE DATES (1|p-batch;r_i|Σw_iT_i)
is NP-complete

INSTANCE: jobs `1, …, n`, each with a processing time `p_j ∈ ℤ⁺`, a release date `r_j`, a due
date `d_j` and a weight `w_j` (nonnegative integers), and a bound `K ∈ ℤ₀⁺`.
QUESTION: is there a parallel-batching schedule on one machine, with no bound on the number of
jobs in a batch and no job started before its release date, whose total weighted tardiness
`∑_j w_j max{0, C_j - d_j}` is at most `K`, where `C_j` is the completion time of job `j`?

Parallel batching is as in `BoundedParallelBatchingReleaseCompletionWanted`
(`1|p-batch;r_i;b<n|ΣC_i`): the jobs are partitioned into batches processed one after another;
all jobs of a batch start together and complete together, and the processing time of a batch is
the largest processing time of its jobs. That module's batch sequence `IsBatchSequence` (job `j`
in batch `B j`, batch `k` started at `S k`) and job completion times `completion` are reused.
This is the unbounded model (`b ≥ n`, Brucker et al. 1998): there is no capacity condition.
Processing times are positive, as in `BoundedParallelBatchingReleaseCompletionWanted`.
Natural-number subtraction truncates at `0`, so `C_j - d_j` is the tardiness
`max{0, C_j - d_j}`.

Hardness: Brucker et al. (1998) prove `1|p-batch|Σw_jT_j` NP-hard; each of its instances is an
instance of this problem with every `r_j = 0` and the same answer, so this problem is NP-hard.
Brucker and Knust's classification (class `bat_p`) lists `1|p-batch;r_i|Σw_iT_i` as maximal
pseudopolynomially solvable, citing Baptiste, Brucker, Knust and Timkovsky (2004); numbers are
in binary encoding. Membership in NP: the batch assignment and the start times form a
certificate, and the earliest start times are at most `max_j r_j + ∑_j p_j`. The jobs are
`Fin n`, one per listed quadruple `(p_j, r_j, d_j, w_j)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNBOUNDED PARALLEL-BATCHING WEIGHTED TARDINESS WITH RELEASE DATES
(`1|p-batch;r_i|Σw_iT_i`) is NP-complete.** Source: Brucker et al. (1998); Brucker and Knust,
class bat_p. -/
public theorem_wanted unboundedParallelBatchingReleaseWeightedTardiness_npComplete :
    unboundedParallelBatchingReleaseWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unboundedParallelBatchingReleaseWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingReleaseWeightedTardiness
