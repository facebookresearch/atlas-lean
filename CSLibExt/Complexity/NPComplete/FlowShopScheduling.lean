/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW-SHOP SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS15] FLOW-SHOP SCHEDULING;
M. R. Garey, D. S. Johnson and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129, doi:10.1287/moor.1.2.117.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs
import CSLibExt.Complexity.NPComplete.FlowShopScheduling.Hardness
import CSLibExt.Complexity.NPComplete.FlowShopScheduling.Membership

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling

/-!
# FLOW-SHOP SCHEDULING is NP-complete

INSTANCE: a number `m ∈ ℤ⁺` of processors, a set `J` of jobs, each job `j ∈ J` consisting of `m`
tasks `t_1[j], t_2[j], …, t_m[j]`, a length `l(t) ∈ ℤ₀⁺` for each such task, and an overall
deadline `D ∈ ℤ⁺`. QUESTION: is there a flow-shop schedule for `J` that meets the overall deadline,
i.e., an open-shop schedule with the additional constraint that, for each `j ∈ J` and
`1 ≤ i < m`, `σ_{i+1}(j) ≥ σ_i(j) + l(t_i[j])`?

The number of processors `m` is part of the instance; `flowShop_npComplete` in
`CSLibExt.Computability.Complexity.Karp.FlowShop` states the special case
`m = 3`. An open-shop schedule is a start time `σ_i(j) ∈ ℤ₀⁺` for each task `t_i[j]` (task
`t_i[j]` runs on processor `i`) such that each processor runs one task at a time, the tasks of a
job do not overlap, and every task ends by `D`. The source's one-processor condition
"`σ_i(j) > σ_i(k)` implies `σ_i(j) ≥ σ_i(k) + l(t_i[k])`" is read as non-overlap of distinct jobs
on processor `i` (`σ_i(j) + l(t_i[j]) ≤ σ_i(k)` or `σ_i(k) + l(t_i[k]) ≤ σ_i(j)`, the form of
`FlowShopFeasible` in `CSLibExt.Computability.Complexity.Karp.FlowShop.Basic`): read literally
it says nothing about two tasks with equal start times. The
open-shop condition that a job's tasks do not overlap follows from the flow-shop constraint, so
it is not repeated. Processors are `Fin m` (`i = 0, …, m - 1`), jobs `Fin |J|`. Binary encoding
of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`). Membership is proved in
`CSLibExt.Complexity.NPComplete.FlowShopScheduling.Membership` (a polynomial-time verifier for
schedules) and NP-hardness in `CSLibExt.Complexity.NPComplete.FlowShopScheduling.Hardness` (a
reduction from the three-processor problem of `CSLibExt.Computability.Complexity.Karp.FlowShop`).
-/

/-- **FLOW-SHOP SCHEDULING is NP-complete.** Source: Garey and Johnson (1979), [SS15];
Garey, Johnson and Sethi (1976). -/
public theorem flowShopScheduling_npComplete :
    flowShopSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L flowShopSchedulingDec :=
  ⟨flowShopScheduling_mem_NP, flowShopScheduling_npHard⟩

end MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling
