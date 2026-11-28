/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR FLOW-SHOP SCHEDULING WITH CHAIN PRECEDENCE CONSTRAINTS is NP-complete

Source:
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X,
Theorem 4(h) in the preprint, Mathematisch Centrum report BW 43/75 (1975),
https://ir.cwi.nl/pub/9725 (KNAPSACK reduces to `n|2|F,tree|Cmax`; the constructed instance has
the single precedence pair `J_{n-1} < J_n`, so it is a chain instance: `F2|chains|Cmax`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Flow-shop problems without preemption" (`F2|chains|Cmax`, minimal NP-hard, credited to
Lenstra, Rinnooy Kan, and Brucker 1977);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS15] FLOW-SHOP SCHEDULING, p. 241
(the parent problem; solvable in polynomial time for `m = 2` without precedence constraints).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorFlowShopChainsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopChains

/-!
# TWO-PROCESSOR FLOW-SHOP SCHEDULING WITH CHAIN PRECEDENCE CONSTRAINTS is NP-complete

INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of `m = 2` tasks `t_1[j]`, `t_2[j]`
(task `t_i[j]` runs on processor `i`), a length `l(t) ∈ ℤ₀⁺` for each such task, a precedence
relation on `J` consisting of disjoint chains (each job has at most one immediate predecessor
and at most one immediate successor), and an overall deadline `D ∈ ℤ⁺`. QUESTION: is there a
flow-shop schedule for `J` that meets the overall deadline (makespan `C_max ≤ D`) such that,
whenever `j` precedes `k`, job `k` starts only after job `j` is completed (`C_j ≤ B_k`)?

This is FLOW-SHOP SCHEDULING ([SS15], `FlowShopScheduling`) with `m = 2` and chain
precedence constraints added (`F2|chains|Cmax`; without precedence constraints the
two-processor problem is solvable in polynomial time, Johnson 1954). The instance type
`FlowShopScheduling.FlowShopSchedulingInstance`, the task lengths `FlowShopScheduling.len` and
`FlowShopScheduling.WellFormed` are the parent's, and the schedule conditions are the parent's
(every task ends by `D`, one task at a time on each processor, each job's tasks in processor
order): meeting the deadline `D` is the makespan bound `C_max ≤ D`. Lenstra, Rinnooy Kan, and
Brucker require `C_j ≤ B_k` for `J_j < J_k`, where `B_k` is the starting time of job `k` (of its
task on the first processor) and `C_j` the completion time of job `j` (of its task on the last
processor).

The chains are given by the list of their arcs `(j, k)`, `j` the immediate predecessor of `k`.
`WellFormed` requires every arc to name two jobs, no two arcs with the same tail or the same
head, and no cycle (the transitive closure `Relation.TransGen` of the arc relation is
irreflexive); the precedence relation is that transitive closure. The constraint is imposed on
the arcs; on the rest of the transitive closure it follows, since every job starts on the first
processor before it completes on the last. Processors are `Fin m` (`i = 0, 1`), jobs `Fin |J|`.
Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR FLOW-SHOP SCHEDULING WITH CHAIN PRECEDENCE CONSTRAINTS is NP-complete.**
Source: Lenstra, Rinnooy Kan, and Brucker (1977), Theorem 4(h); Brucker and Knust's
classification (`F2|chains|Cmax`). -/
public theorem_wanted twoProcessorFlowShopChains_npComplete :
    twoProcessorFlowShopChainsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorFlowShopChainsDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopChains
