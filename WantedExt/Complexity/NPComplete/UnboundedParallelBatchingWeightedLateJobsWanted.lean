/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNBOUNDED PARALLEL-BATCHING WEIGHTED NUMBER OF LATE JOBS (1|p-batch|Σw_iU_i) is NP-complete

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (`1|p-batch|Σw_jU_j` NP-hard);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch|Σw_iU_i`: minimal NP-hard in the ordinary sense.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnboundedParallelBatchingReleaseWeightedLateJobsWanted
public import WantedExt.Complexity.NPComplete.UnboundedParallelBatchingWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingWeightedLateJobs

open UnboundedParallelBatchingReleaseWeightedTardiness
  (UnboundedParallelBatchingReleaseWeightedTardinessInstance)
open UnboundedParallelBatchingReleaseWeightedLateJobs
  (UnboundedParallelBatchingReleaseWeightedLateJobsFeasible)
open UnboundedParallelBatchingWeightedTardiness (WellFormed)

/-!
# UNBOUNDED PARALLEL-BATCHING WEIGHTED NUMBER OF LATE JOBS (1|p-batch|Σw_iU_i) is NP-complete

INSTANCE: jobs `1, …, n`, each with a processing time `p_j ∈ ℤ⁺`, a due date `d_j` and a weight
`w_j` (nonnegative integers), and a bound `K ∈ ℤ₀⁺`.
QUESTION: is there a parallel-batching schedule on one machine, with no bound on the number of
jobs in a batch, in which the total weight of the late jobs, the jobs `j` with `C_j > d_j`, is
at most `K`, where `C_j` is the completion time of job `j`?

This is `1|p-batch;r_i|Σw_iU_i` (`UnboundedParallelBatchingReleaseWeightedLateJobsWanted`)
with every release date `0`. The instance (jobs as quadruples `(p_j, r_j, d_j, w_j)` and the
bound `K`) and the question are reused from that module, and the well-formedness (positive
processing times, every release date `0`, so the release condition holds for every schedule)
from `UnboundedParallelBatchingWeightedTardinessWanted` (`1|p-batch|Σw_iT_i`). Parallel batching
with unbounded batch size is as there: the jobs are partitioned into batches processed one after
another, all jobs of a batch start together and complete together, and the processing time of a
batch is the largest processing time of its jobs.

Brucker et al. (1998) prove the problem NP-hard; Brucker and Knust list it as minimal NP-hard in
the ordinary sense, so numbers are in binary encoding. Membership in NP: the batch assignment
and the start times form a certificate, and the earliest start times are at most `∑_j p_j`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- UNBOUNDED PARALLEL-BATCHING WEIGHTED NUMBER OF LATE JOBS as a decision problem over
bitstrings. -/
noncomputable def unboundedParallelBatchingWeightedLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnboundedParallelBatchingReleaseWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ UnboundedParallelBatchingReleaseWeightedLateJobsFeasible i)
  | none => false

/-- **UNBOUNDED PARALLEL-BATCHING WEIGHTED NUMBER OF LATE JOBS (`1|p-batch|Σw_iU_i`) is
NP-complete.** Source: Brucker et al. (1998); Brucker and Knust, class bat_p. -/
public theorem_wanted unboundedParallelBatchingWeightedLateJobs_npComplete :
    unboundedParallelBatchingWeightedLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unboundedParallelBatchingWeightedLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingWeightedLateJobs
