/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|prec;p_i=1;p-batch;b<n|C_max` is NP-complete

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel batching problems"
(`1|prec;p_i=1;p-batch;b<n|C_max`, minimal NP-hard in the strong sense,
by reduction from the parallel machine problem `P|prec;p_i=1|C_max`);
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0 (`P|prec;p_i=1|C_max`; Garey and Johnson,
[SS9]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingMakespan

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance PrecedenceConstrainedSchedulingFeasible)

/-!
# PARALLEL BATCHING `1|prec;p_i=1;p-batch;b<n|C_max` is NP-complete

INSTANCE: `n` jobs, each with unit processing time `p_i = 1`, to be processed in batches on a
single machine; a batch capacity `b ∈ ℤ⁺` with `b < n`; a precedence relation (a partial order)
on the jobs: if `i` precedes `j`, then `j` cannot start before `i` is completed; and a bound
`K`. QUESTION: is there a feasible schedule with makespan `max_i C_i ≤ K`, where `C_i` is the
completion time of job `i`?

Parallel batching (Brucker et al. 1998; Brucker and Knust): the jobs are processed on a single
machine in batches of at most `b` jobs, one batch after another; all jobs of a batch start and
complete at the same time, and the processing time of a batch is the largest processing time of
its jobs, here `1`. A schedule is given by the start time `σ(t)` of the batch of each job `t`:
the jobs with the same start time form one batch, which occupies `[σ(t), σ(t) + 1)`, so batches
with different integral start times do not overlap, and a batch holds at most `b` jobs. For a
fixed sequence of batches the earliest start times are integral and no later than any other
start times, so integral start times lose no generality. The bounded case `b < n` (`n` jobs) is
part of the instance class.

The instance data are those of PRECEDENCE CONSTRAINED SCHEDULING ([SS9],
`PrecedenceConstrainedSchedulingWanted`), reused unchanged: the job lengths (all `1`), a number
read here as the batch capacity `b` (that module's number `m` of processors), the listed pairs
`(t, t')` with `t` preceding `t'` (required to form a strict partial order), and the bound `K`
(that module's deadline `D`, required to be positive). Its question is reused as well: some
`σ` has at most `b` jobs running at each time (`running`; with unit jobs these are the jobs of
the batch started then), obeys the precedence constraints (`σ(t) + 1 ≤ σ(t')`) and completes
every job by `K`. `WellFormed` adds `b < n`. Binary encoding of all numbers (the problem is
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

/-- Well-formedness of an instance: it is well-formed for PRECEDENCE CONSTRAINED SCHEDULING (unit
lengths, `b > 0`, the listed pairs name jobs and form a strict partial order, `K > 0`), and the
batch capacity is bounded: `b < n`. -/
def WellFormed (i : PrecedenceConstrainedSchedulingInstance) : Prop :=
  PrecedenceConstrainedScheduling.WellFormed i ∧ i.2.1 < i.1.length

open Classical in
/-- `1|prec;p_i=1;p-batch;b<n|C_max` as a decision problem over bitstrings. -/
noncomputable def unitPrecedenceParallelBatchingMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceConstrainedSchedulingFeasible i)
  | none => false

/-- **PARALLEL BATCHING `1|prec;p_i=1;p-batch;b<n|C_max` is NP-complete.** Source: Brucker and
Knust's classification (reduction from `P|prec;p_i=1|C_max`, Ullman 1975). -/
public theorem_wanted unitPrecedenceParallelBatchingMakespan_npComplete :
    unitPrecedenceParallelBatchingMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitPrecedenceParallelBatchingMakespanDec

end MetaMathlibExt.Complexity.NPComplete.UnitPrecedenceParallelBatchingMakespan
