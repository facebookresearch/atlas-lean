/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK JOB SHOP JMPT2|chains;p_ij=1|ΣC_i is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8
(`J2|chains, p_ij = 1|∑ C_j` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `mpt_shop` (shop problems with multiprocessor tasks), Universität Osnabrück, which lists
`JMPT2|chains; p_ij = 1|∑ C_i` as minimal NP-hard in the strong sense, citing Timkovsky (1998);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the multiprocessor-task model) and Section 1.3 (chains).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopChainsCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopChainsCompletionTime

open UnitMultiPurposeJobShopMakespan (UnitMultiPurposeJobShopInstance Operation)
open UnitMultiprocessorTaskJobShopMakespan (IsUnitMPTSchedule)

/-!
# MULTIPROCESSOR-TASK JOB SHOP JMPT2|chains;p_ij=1|ΣC_i is NP-complete

INSTANCE: `m = 2` processors `M₁, M₂`; jobs, each a chain of `n_j ≥ 1` multiprocessor tasks
`O_{j1}, …, O_{jn_j}` with unit processing times, where task `O_{jk}` requires simultaneously
all processors of a given nonempty set `μ_{jk} ⊆ {M₁, M₂}`; tasks requiring a common processor
cannot be processed simultaneously, and `O_{j,k+1}` cannot start before `O_{jk}` is completed; a
precedence relation on the jobs consisting of disjoint chains (each job has at most one immediate
predecessor and at most one immediate successor); a bound `K`. QUESTION: is there a schedule in
which, whenever `j` precedes `j'`, the first task of `j'` starts no earlier than the last task of
`j` completes, and whose total completion time `∑_j C_j` is at most `K`, `C_j` being the
completion time of the last task of `j`?

This is the multiprocessor-task job shop of Brucker (*Scheduling Algorithms*, Chapter 11: every
task occupies all processors of its set, tasks requiring a common processor are incompatible,
and every job is a chain of tasks) with chain precedence constraints between jobs (Section 1.3).
Brucker and Knust list `JMPT2|chains; p_ij = 1|∑ C_i` as minimal NP-hard in the strong sense,
citing Timkovsky (1998), who proves the dedicated-processor case `J2|chains, p_ij = 1|∑ C_j`
NP-hard in the strong sense: that is the special case in which every task requires a single
processor and consecutive tasks of a job require different processors. Membership in NP: the
start times are a certificate.

The instance, tasks, well-formedness and schedules are those of
`UnitMultiprocessorTaskJobShopMakespanWanted` (`JMPT2|p_ij = 1|C_max`): the instance
`UnitMultiPurposeJobShopInstance` (the number `m` of processors, the jobs as lists of their tasks,
each task given by the list of processors it requires, and in the last place the bound `K`), its
`WellFormed` (`m = 2`, every job has a task, every processor set is nonempty and lies in
`{1, 2}`) and `IsUnitMPTSchedule` (natural start times, tasks sharing a processor start at
different times, the tasks of a job in order). The chains are given by the list of their arcs
`(j, j')`, `j` the immediate predecessor of `j'`. `WellFormed` requires every arc to name two jobs,
no two arcs with the same tail or the same head, and no cycle (the transitive closure
`Relation.TransGen` of the arc relation is irreflexive); the precedence relation is that
transitive closure. The constraint is imposed on the arcs; on the rest of the transitive closure
it follows, since every job starts its first task before it completes its last. Binary encoding
of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIPROCESSOR-TASK JOB SHOP `JMPT2|chains;p_ij=1|ΣC_i` is NP-complete.** Source: Timkovsky
(1998); Brucker and Knust, scheduling classification, class `mpt_shop`; Brucker (2007),
Chapter 11. -/
public theorem_wanted unitMultiprocessorTaskJobShopChainsCompletionTime_npComplete :
    unitMultiprocessorTaskJobShopChainsCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitMultiprocessorTaskJobShopChainsCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopChainsCompletionTime
