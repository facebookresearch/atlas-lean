/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|Σw_iC_i` is NP-complete

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel batching problems"
(`1|chains;p_i=1;p-batch;b<n|Σw_iC_i`, minimal NP-hard in the strong sense,
by reduction from the parallel machine problem);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (`P2|p_i=1;chains|Σw_iC_i`, NP-hard in the strong sense, as
recorded by Brucker and Knust, class "Parallel machine problems without preemption", and by
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 5.3; the full text was
not available to us).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TwoProcessorUnitChainsWeightedCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingWeightedCompletion

open MetaMathlibExt.Complexity.NPComplete.TwoProcessorTreePrecedenceCompletionTime
  (TwoProcessorTreePrecedenceCompletionTimeInstance
    TwoProcessorTreePrecedenceCompletionTimeFeasible)

/-!
# PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|Σw_iC_i` is NP-complete

INSTANCE: `n` jobs, each with unit processing time `p_i = 1` and a weight `w_i ∈ ℤ₀⁺`, to be
processed in batches on a single machine; a batch capacity `b ∈ ℤ⁺` with `b < n`; a precedence
relation on the jobs consisting of chains (every job has at most one immediate predecessor and
at most one immediate successor): if `i` precedes `j`, then `j` cannot start before `i` is
completed; and a bound `K`. QUESTION: is there a feasible schedule with total weighted
completion time `Σ_i w_i C_i ≤ K`, where `C_i` is the completion time of job `i`?

Parallel batching (Brucker et al. 1998; Brucker and Knust): the jobs are processed on a single
machine in batches of at most `b` jobs, one batch after another; all jobs of a batch start and
complete at the same time, and the processing time of a batch is the largest processing time of
its jobs, here `1`. A schedule is given by the start time `σ(t)` of the batch of each job `t`:
the jobs with the same start time form one batch, which occupies `[σ(t), σ(t) + 1)`, so batches
with different integral start times do not overlap, and a batch holds at most `b` jobs. For a
fixed sequence of batches the earliest start times are integral and no later than any other
start times, so integral start times lose no generality. The bounded case `b < n` (`n` jobs) is
part of the instance class.

Brucker and Knust derive the strong NP-hardness of this problem from the parallel machine
problem: with unit processing times, a batch of at most `b` jobs is a time slot on `b` identical
parallel machines. Its case `b = 2` is `P2|p_i=1;chains|Σw_iC_i`
(`TwoProcessorUnitChainsWeightedCompletionWanted`), which Brucker and Knust and Brucker's
Table 5.3 list as NP-hard in the strong sense, crediting Timkovsky (2003).

The instance and the question are those of `P2|p_i=1;chains|Σw_iC_i`, reused unchanged with
that module's number `m` of processors read as the batch capacity `b`: one pair `(p_i, w_i)`
per job, the number `b`, the bound `K`, and the listed pairs `(t, t')` with `t` preceding `t'`;
the question (`TwoProcessorTreePrecedenceCompletionTimeFeasible`) asks for start times
`σ(t) ∈ ℤ₀⁺` such that at most `b` jobs run at each time (with unit jobs, the jobs of the batch
started then), `t` preceding `t'` implies `σ(t) + 1 ≤ σ(t')`, and
`Σ_t (σ(t) + 1) · w_t ≤ K`. `WellFormed` is that problem's well-formedness for the instance
with `b` replaced by `2` (unit processing times, the listed pairs name jobs and form a strict
partial order consisting of chains; that well-formedness reads the number of processors only to
require it to be `2`), together with `0 < b < n`. Weights and `K` are arbitrary natural numbers
(a negative `K` gives only no-instances). Closing an empty time slot (moving every later batch
one step earlier) keeps a schedule feasible without increasing `Σ_i w_i C_i`, so start times
below `n` form a certificate of polynomial size. Binary encoding of all numbers (the problem is
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

/-- Well-formedness of an instance: with its batch capacity replaced by `2`, it is well formed
for `P2|p_i=1;chains|Σw_iC_i` (unit processing times, the listed pairs name jobs and form a
strict partial order consisting of chains), and the batch capacity satisfies `0 < b < n`. -/
def WellFormed (i : TwoProcessorTreePrecedenceCompletionTimeInstance) : Prop :=
  TwoProcessorUnitChainsWeightedCompletion.WellFormed (2, i.2) ∧ 0 < i.1 ∧
    i.1 < i.2.1.length

open Classical in
/-- `1|chains;p_i=1;p-batch;b<n|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def chainsUnitParallelBatchingWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTreePrecedenceCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTreePrecedenceCompletionTimeFeasible i)
  | none => false

/-- **PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|Σw_iC_i` is NP-complete.** Source: Brucker
and Knust's classification (reduction from the parallel machine problem
`P2|p_i=1;chains|Σw_iC_i`, Timkovsky 2003). -/
public theorem_wanted chainsUnitParallelBatchingWeightedCompletion_npComplete :
    chainsUnitParallelBatchingWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chainsUnitParallelBatchingWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingWeightedCompletion
