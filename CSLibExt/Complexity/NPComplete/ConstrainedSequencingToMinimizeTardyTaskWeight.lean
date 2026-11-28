/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT;
D. Zuckerman, "On unapproximable versions of NP-complete problems", SIAM Journal on Computing
25 (1996), 1293-1304, doi:10.1137/S0097539794266407, Theorem 3.1, problem 19 (CONSTRAINED MAX
JOB SEQUENCING); conference version: Proc. 8th Annual Structure in Complexity Theory Conference
(1993), 305-312, doi:10.1109/SCT.1993.336517;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS3] SEQUENCING TO MINIMIZE TARDY TASK WEIGHT
(the unconstrained problem, an antecedent);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (JOB SEQUENCING, the unconstrained problem, an antecedent).
-/
module

public import CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeightDefs
public import CSLibExt.Computability.Complexity.Defs
import CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight.Hardness
import CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight.Membership

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight

/-!
# CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT is NP-complete

INSTANCE: a set `T` of tasks, for each task `t ∈ T` a length `l(t) ∈ ℤ⁺`, a weight
`w(t) ∈ ℤ⁺` and a deadline `d(t) ∈ ℤ⁺`, a subset `S ⊆ T`, a positive integer `K`, and a
positive integer `J`. QUESTION: is there a one-processor schedule `σ` for `T` such that the
sum of `w(t)` over the tasks `t` with `σ(t) + l(t) > d(t)` is at most `K`, and at least `J`
tasks of `S` are completed by their deadlines?

This is the decision version of MAXIMUM CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT in
the compendium of Crescenzi and Kann (Zuckerman's CONSTRAINED MAX JOB SEQUENCING), whose
measure is the number of tasks of `S` completed by their deadlines. The compendium names both
the tardy-weight bound of the instance and the bound of the decision version `K`; here the
second one is `J`.

The tasks, the bound `K` and the schedule reuse `WeightedTardyJobs`
(`CSLibExt.Computability.Complexity.Karp.WeightedTardyJobs`; SEQUENCING TO
MINIMIZE TARDY TASK WEIGHT, [SS3]): a task is a triple (length, deadline, weight), a schedule is
an ordering of the task indices processed without idle time, and `WeightedTardy` is the total
weight of the tasks completing after their deadlines. `S` is a list of task indices (a repeated
index denotes the same task). A task is completed by its deadline when its completion time
`σ(t) + l(t)` is at most `d(t)`. The numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`). Membership is proved in
`CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight.Membership`
(a polynomial-time verifier for skip/take plans) and NP-hardness in
`CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight.Hardness`
(a reduction from PARTITION).
-/

/-- **CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT is NP-complete.** Source: Crescenzi
and Kann, MAXIMUM CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT; Zuckerman (1996),
problem 19. The unconstrained problem is Garey and Johnson (1979), [SS3], and Karp (1972). -/
public theorem constrainedSequencing_npComplete :
    constrainedSequencingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L constrainedSequencingDec :=
  ⟨constrainedSequencing_mem_NP, constrainedSequencing_npHard⟩

end MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight
