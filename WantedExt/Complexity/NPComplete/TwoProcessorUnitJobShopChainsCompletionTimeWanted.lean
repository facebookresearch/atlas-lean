/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR UNIT-TIME JOB-SHOP TOTAL COMPLETION TIME WITH CHAINS is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8
(`J2|chains, pᵢⱼ = 1|∑ Cⱼ` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Job-shop problems without preemption" (`J2|chains; pᵢⱼ = 1|∑ Cᵢ`, minimal NP-hard,
credited to Timkovsky 1998);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitJobShopChainsCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitJobShopChainsCompletionTime

open JobShopScheduling (JobShopSchedulingInstance taskLength taskProcessor)

/-!
# TWO-PROCESSOR UNIT-TIME JOB-SHOP TOTAL COMPLETION TIME WITH CHAINS is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting of an ordered
collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, each of length `l(t) = 1` and with a processor
`p(t) ∈ {1, 2}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])`, a precedence relation on `J` consisting of
disjoint chains (each job has at most one immediate predecessor and at most one immediate
successor), and a bound `K ∈ ℤ⁺`. QUESTION: is there a job-shop schedule for `J` in which,
whenever `j` precedes `j'`, the first task of `j'` starts no earlier than the last task of `j`
finishes, and whose total completion time `∑_{j ∈ J} C_j` is at most `K`, `C_j` being the time
the last task of `j` finishes?

This is `J2|chains; pᵢⱼ = 1|∑ Cᵢ`: JOB-SHOP SCHEDULING ([SS18], `JobShopSchedulingDefs`) with `m =
2`, unit task lengths, chain precedence constraints between jobs, and the deadline replaced by a
bound `K` on the total completion time. Timkovsky (1998) proves it NP-hard in the strong sense with
his job-shopping theorem, which reduces preemptive identical parallel machines to unit-time job
shops. The instance type `JobShopScheduling.JobShopSchedulingInstance`,
`JobShopScheduling.WellFormed` (which includes `n_j ≥ 1`), the tasks and their lengths and
processors are the parent's; the last component of the instance is the bound `K ∈ ℤ⁺` in place of
the deadline `D ∈ ℤ⁺`. The schedule conditions are the parent's (one-to-one start times on each
processor, one task at a time on each processor, the tasks of a job in order), with the parent's
deadline condition replaced by the bound on `∑ C_j`, where `C j` is pinned to the finishing time of
the last task of `j` (every job has a task, `n_j ≥ 1`). Unit lengths are a well-formedness
condition.

The chains are given by the list of their arcs `(j, j')`, `j` the immediate predecessor of
`j'`. `WellFormed` requires every arc to name two jobs, no two arcs with the same tail or the
same head, and no cycle (the transitive closure `Relation.TransGen` of the arc relation is
irreflexive); the precedence relation is that transitive closure. The constraint is imposed
on the arcs; on the rest of the transitive closure it follows, since every job starts its
first task before it finishes its last. Task positions are numbered from `0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR UNIT-TIME JOB-SHOP TOTAL COMPLETION TIME WITH CHAINS is
NP-complete.** Source: Timkovsky (1998); Brucker and Knust's classification
(`J2|chains; pᵢⱼ = 1|∑ Cᵢ`). -/
public theorem_wanted twoProcessorUnitJobShopChainsCompletionTime_npComplete :
    twoProcessorUnitJobShopChainsCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitJobShopChainsCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitJobShopChainsCompletionTime
