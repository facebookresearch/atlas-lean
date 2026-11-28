/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP WITH TREE PRECEDENCE AND UNIT TIMES (FMPT|tree; p_ij = 1|L_max) is NP-complete

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT|tree; p_ij = 1|L_max` as minimal NP-hard in the strong sense with the
attribution to Brucker and Knust (1999);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (the MPT flow-shop
model) and Section 1.3 (precedence relations).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLateness

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed UnitJobs)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTPrecedenceSchedule)

/-!
# MPT FLOW SHOP WITH TREE PRECEDENCE AND UNIT TIMES (FMPT|tree; p_ij = 1|L_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; a flow shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and machine sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `1, …, n`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij`
requires every machine of `μ_j` during its processing and `O_i,j+1` cannot start before `O_ij`
is completed; a due date `d_i ∈ ℤ` for each job `i`; a precedence relation `→` on the jobs that
is a tree (an intree or an outtree); and a bound `K ∈ ℤ`. Operations requiring a common machine
cannot be processed simultaneously. QUESTION: is there a feasible schedule whose maximum
lateness `max_i (C_i - d_i)` is at most `K`, where `C_i` is the completion time of job `i` (that
of its last operation)?

The MPT flow shop, its stage machine sets, unit-time schedules and job precedence are those of
`MultiprocessorTaskFlowShopPrecedenceMakespanWanted` (`FMPT|prec; p_ij = 1|C_max`), reused here:
`StagesWellFormed`, `UnitJobs`, `Prec` and `PrecWellFormed` (the arcs `(i, k)` with `i → k` of
an acyclic digraph) and `IsMPTPrecedenceSchedule`. Following Brucker (*Scheduling Algorithms*,
Section 1.3), `tree` means that the precedence graph is either an intree (every job has at most
one successor) or an outtree (every job has at most one predecessor); a set of chains is a tree,
so forests are included. The tree condition is checked on the immediate predecessors of the
precedence relation: `i` is an immediate predecessor of `k` when `k` is reachable from `i` along
arcs and no job `c` lies strictly between them. Arcs implied by transitivity may therefore be
listed or omitted; they constrain the same schedules, since a job completes after it starts. The
maximum lateness bound is stated as `C_i - d_i ≤ K` for every job `i`; there is at least one job,
since `max_i (C_i - d_i)` is undefined for an empty job set. Due dates and `K` are integers given
as `(positive part, negative part)` pairs. Binary encoding of all numbers.

Brucker and Knust's flow-shop table lists `F|p_ij = 1; outtree|L_max` as strongly NP-hard
(Brucker and Knust 1999); it is the special case `r = m`, `μ_j = {M_j}` with an outtree of this
problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`FMPT|tree; p_ij = 1|L_max` is NP-complete.** Source: Brucker and Knust (1999); Brucker
and Knust, *Complexity results for scheduling problems*; Brucker (2004), Chapter 11. -/
public theorem_wanted multiprocessorTaskFlowShopTreeLateness_npComplete :
    multiprocessorTaskFlowShopTreeLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskFlowShopTreeLatenessDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLateness
