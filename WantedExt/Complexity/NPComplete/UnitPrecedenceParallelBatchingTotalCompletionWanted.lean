/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|prec;p_i=1;p-batch;b<n|ΣC_i` is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingTotalCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance)
open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingTotalCompletion
  (PrecedenceConstrainedSchedulingTotalCompletionFeasible)
open MetaMathlibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingMakespan (WellFormed)

/-!
# PARALLEL BATCHING `1|prec;p_i=1;p-batch;b<n|ΣC_i` is NP-complete

INSTANCE: `n` jobs, each with unit processing time `p_i = 1`, to be processed in batches on a
single machine; a batch capacity `b ∈ ℤ⁺` with `b < n`; a precedence relation (a partial order)
on the jobs: if `i` precedes `j`, then `j` cannot start before `i` is completed; and a bound
`K`. QUESTION: is there a feasible schedule with total completion time `Σ_i C_i ≤ K`, where
`C_i` is the completion time of job `i`?

Parallel batching (Brucker et al. 1998; Brucker and Knust): the jobs are processed on a single
machine in batches of at most `b` jobs, one batch after another; all jobs of a batch start and
complete at the same time, and the processing time of a batch is the largest processing time of
its jobs, here `1`. As in `UnitPrecedenceParallelBatchingMakespanWanted`
(`1|prec;p_i=1;p-batch;b<n|C_max`), a schedule is given by the start time `σ(t)` of the batch
of each job `t`: the jobs with the same start time form one batch, which occupies
`[σ(t), σ(t) + 1)`, so batches with different integral start times do not overlap, and a batch
holds at most `b` jobs. For a fixed sequence of batches the earliest start times are integral
and no later than any other start times, so integral start times lose no generality.

The instance data and well-formedness are those of `UnitPrecedenceParallelBatchingMakespanWanted`,
reused unchanged: the data of PRECEDENCE CONSTRAINED SCHEDULING ([SS9],
`PrecedenceConstrainedSchedulingWanted`) with its number `m` of processors read as the batch
capacity `b` and its last number as the bound `K`, its well-formedness (unit lengths, `b > 0`,
the listed pairs name jobs and form a strict partial order, `K > 0`), and the bounded case
`b < n`. The question is that of `P|prec;p_i=1|ΣC_i`
(`PrecedenceConstrainedSchedulingTotalCompletionWanted`), reused as well: some `σ` has at most
`b` jobs running at each time (with unit jobs these are the jobs of the batch started then),
obeys the precedence constraints (`σ(t) + 1 ≤ σ(t')`) and has `Σ_t (σ(t) + 1) ≤ K`. Binary
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

/-- **PARALLEL BATCHING `1|prec;p_i=1;p-batch;b<n|ΣC_i` is NP-complete.** Source: Brucker and
Knust's classification (reduction from `P|prec;p_i=1|ΣC_i`, Lenstra and Rinnooy Kan 1978). -/
public theorem_wanted unitPrecedenceParallelBatchingTotalCompletion_npComplete :
    unitPrecedenceParallelBatchingTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitPrecedenceParallelBatchingTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingTotalCompletion
