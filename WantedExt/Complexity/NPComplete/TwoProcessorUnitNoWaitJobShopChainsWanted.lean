/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING WITH CHAINS is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8
(`J2|chains, pᵢⱼ = 1, no-wait|C_max` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Job-shop problems with no-wait" (`J2|chains; pᵢⱼ = 1; no-wait|C_max`, minimal NP-hard,
credited to Timkovsky 1998);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitNoWaitJobShopChainsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitNoWaitJobShopChains

open JobShopScheduling (JobShopSchedulingInstance taskLength taskProcessor)

/-!
# TWO-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING WITH CHAINS is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting of an ordered
collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, each of length `l(t) = 1` and with a processor
`p(t) ∈ {1, 2}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])`, a precedence relation on `J` consisting of
disjoint chains (each job has at most one immediate predecessor and at most one immediate
successor), and a deadline `D ∈ ℤ⁺`. QUESTION: is there a job-shop schedule for `J` that meets
the overall deadline (makespan `C_max ≤ D`), in which every task of a job starts exactly when
the previous task of that job finishes (no wait), and in which, whenever `j` precedes `j'`,
the first task of `j'` starts no earlier than the last task of `j` finishes?

This is `J2|chains; pᵢⱼ = 1; no-wait|C_max`: JOB-SHOP SCHEDULING ([SS18], `JobShopSchedulingDefs`)
with `m = 2`, unit task lengths, the no-wait condition and chain precedence constraints between
jobs. Timkovsky (1998) proves it NP-hard in the strong sense with his job-shopping theorem, a
reduction of nonpreemptive identical parallel machines to no-wait unit-time job shops. The instance
type `JobShopScheduling.JobShopSchedulingInstance`, `JobShopScheduling.WellFormed` (which includes
`n_j ≥ 1`), the tasks and their lengths and processors are the parent's, and so are the schedule
conditions (one-to-one start times on each processor, one task at a time on each processor, every
job finished by `D`), except that the parent's job-order condition `σ(t_{k+1}[j]) ≥ σ(t_k[j]) +
l(t_k[j])` is strengthened to equality (no wait). Unit lengths are a well-formedness condition.

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

/-- **TWO-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING WITH CHAINS is NP-complete.** Source:
Timkovsky (1998); Brucker and Knust's classification (`J2|chains; pᵢⱼ = 1; no-wait|C_max`). -/
public theorem_wanted twoProcessorUnitNoWaitJobShopChains_npComplete :
    twoProcessorUnitNoWaitJobShopChainsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitNoWaitJobShopChainsDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitNoWaitJobShopChains
