/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH TREE PRECEDENCE AND UNIT TIMES (OMPT|tree; p_ij = 1|L_max) is NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT|tree; p_ij = 1|L_max` as minimal NP-hard in the strong sense with the
attribution to Timkovsky (2003);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (the MPT open-shop
model) and Section 1.3 (precedence relations).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTreeLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTreeLateness

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopPrecedenceSchedule)
open MultiprocessorTaskFlowShopTreeLateness
  (MultiprocessorTaskFlowShopTreeLatenessInstance dueDate bound WellFormed)

/-!
# MPT OPEN SHOP WITH TREE PRECEDENCE AND UNIT TIMES (OMPT|tree; p_ij = 1|L_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an open shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and machine sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `1, …, n`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij`
requires every machine of `μ_j` during its processing and the operations of a job may be
processed in any order, but no two of them at the same time; a due date `d_i ∈ ℤ` for each job
`i`; a precedence relation `→` on the jobs that is a tree (an intree or an outtree); and a bound
`K ∈ ℤ`. Operations requiring a common machine cannot be processed simultaneously. QUESTION: is
there a feasible schedule whose maximum lateness `max_i (C_i - d_i)` is at most `K`, where `C_i`
is the completion time of job `i` (that of its last operation)?

The instance, its well-formedness and the due dates and bound are those of the MPT flow shop
`FMPT|tree; p_ij = 1|L_max` (`MultiprocessorTaskFlowShopTreeLatenessWanted`): the stage machine
sets, the unit-time jobs listed with their due dates, the arcs `(i, k)` with `i → k` of an
acyclic digraph whose immediate-predecessor relation is an intree or an outtree (Brucker,
Section 1.3; forests included; arcs implied by transitivity may be listed or omitted), at least
one job (the maximum over an empty job set is undefined), and due dates and `K` given as
`(positive part, negative part)` pairs. Only the schedule differs: it is the unit-time MPT
open-shop schedule with precedence `IsMPTOpenShopPrecedenceSchedule` of
`MultiprocessorTaskOpenShopPrecedenceMakespanWanted` (`OMPT|prec; p_ij = 1|C_max`), in which the
operations of a job have no prescribed order. The maximum lateness bound is stated as
`C_i - d_i ≤ K` for every job `i`. Binary encoding of all numbers.

OMPT is Brucker's stage model (*Scheduling Algorithms*, Chapter 11), as in the base module
`MultiprocessorTaskOpenShopPrecedenceMakespanWanted`: as in the MPT flow shop, every job has one
task per stage `j`, and the task of stage `j` needs the processor set `μ_j`. Brucker states the
polynomial cases of the class as `OMPT|p_ij = 1; stages = r|…`, with the number `r` of stages as a
parameter, and his algorithm for them fixes, for each order of the stages, how many jobs pass the
stages in that order, which presupposes stage-dependent sets; task-dependent sets `μ_ij` with no
precedence between the tasks of a job are the general shop with MPT. A stage set may be empty, as
`μ_j ⊆ {M_1, …, M_m}` allows; the classical special case `μ_j = {M_j}`, which carries the
NP-hardness, has nonempty sets.

Brucker and Knust's open-shop table lists `O|p_ij = 1; outtree|L_max` as strongly NP-hard
(Timkovsky 2003, whose paper was not available to this formalization); it is the special case
`r = m`, `μ_j = {M_j}` with an outtree of this problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`OMPT|tree; p_ij = 1|L_max` is NP-complete.** Source: Timkovsky (2003); Brucker and
Knust, *Complexity results for scheduling problems*; Brucker (2004), Chapter 11. -/
public theorem_wanted multiprocessorTaskOpenShopTreeLateness_npComplete :
    multiprocessorTaskOpenShopTreeLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopTreeLatenessDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTreeLateness
