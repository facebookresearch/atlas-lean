/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|ΣT_i` is NP-complete

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel batching problems"
(`1|chains;p_i=1;p-batch;b<n|ΣT_i`, minimal NP-hard in the strong sense,
by reduction from the single machine problem `1|chains;p_i=1|ΣT_i`);
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with
precedence constraints", ORSA Journal on Computing 2 (1990), 346-352,
doi:10.1287/ijoc.2.4.346 (`1|chains, p_j = 1|ΣT_j`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChainsUnitParallelBatchingTotalTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingTotalTardiness

open MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitTaskTardiness
  (PrecedenceUnitTaskTardinessInstance Prec)
open MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardiness
  (Task taskLength weight deadline)

/-!
# PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|ΣT_i` is NP-complete

INSTANCE: `n` jobs, each with unit processing time `p_i = 1` and a due date `d_i`, to be
processed in batches on a single machine; a batch capacity `b ∈ ℤ⁺` with `b < n`; a precedence
relation on the jobs consisting of chains (every job has at most one immediate predecessor and
at most one immediate successor): if `i` precedes `j`, then `j` cannot start before `i` is
completed; and a bound `K`. QUESTION: is there a feasible schedule whose total tardiness
`Σ_i T_i` is at most `K`, where `T_i = max(0, C_i - d_i)` for the completion time `C_i` of job
`i`?

Parallel batching (Brucker et al. 1998; Brucker and Knust): the jobs are processed on a single
machine in batches of at most `b` jobs, one batch after another; all jobs of a batch start and
complete at the same time, and the processing time of a batch is the largest processing time of
its jobs, here `1`. A schedule is given by the start time `σ(t)` of the batch of each job `t`:
the jobs with the same start time form one batch, which occupies `[σ(t), σ(t) + 1)`, so batches
with different integral start times do not overlap, and a batch holds at most `b` jobs. For a
fixed sequence of batches the earliest start times are integral and no later than any other
start times, so integral start times lose no generality. The bounded case `b < n` (`n` jobs) is
part of the instance class.

The instance extends that of `1|chains, p_j = 1|ΣT_j` (`ChainsUnitTaskTardinessWanted`, the case
of a single job per time slot, `b = 1`) by the batch capacity `b`; that module's job data (length,
weight and due date of each job), precedence relation (the listed pairs `(t, t')` with `t`
preceding `t'`) and well-formedness (unit lengths and unit weights, positive due dates and
positive `K`, a strict partial order that is chain-like) are reused unchanged, and `WellFormed`
adds `0 < b < n`. The tardiness sum is written as in that module, over the late jobs, with the
weights, all `1`. Binary encoding of all numbers (the problem is NP-complete in the strong
sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|ΣT_i` is NP-complete.** Source: Brucker and
Knust's classification (reduction from `1|chains;p_i=1|ΣT_i`, Leung and Young 1990). -/
public theorem_wanted chainsUnitParallelBatchingTotalTardiness_npComplete :
    chainsUnitParallelBatchingTotalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chainsUnitParallelBatchingTotalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingTotalTardiness
