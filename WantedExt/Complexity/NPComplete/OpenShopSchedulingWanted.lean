/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN-SHOP SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING;
T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time", Journal of the ACM 23
(1976), 665-679, doi:10.1145/321978.321985.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.NoWaitFlowShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling

/-!
# OPEN-SHOP SCHEDULING is NP-complete

INSTANCE: a number `m ∈ ℤ⁺` of processors, a set `J` of jobs, each job `j ∈ J` consisting of `m`
tasks `t_1[j], t_2[j], …, t_m[j]` (with `t_i[j]` to be executed by processor `i`), a length
`l(t) ∈ ℤ₀⁺` for each such task `t`, and an overall deadline `D ∈ ℤ⁺`. QUESTION: is there an
open-shop schedule for `J` that meets the deadline, i.e., a collection of one-processor schedules
`σ_i : J → ℤ₀⁺`, `1 ≤ i ≤ m`, such that `σ_i(j) > σ_i(k)` implies `σ_i(j) ≥ σ_i(k) + l(t_i[k])`,
such that for each `j ∈ J` the intervals `[σ_i(j), σ_i(j) + l(t_i[j]))` are all disjoint, and
such that `σ_i(j) + l(t_i[j]) ≤ D` for `1 ≤ i ≤ m`, `1 ≤ j ≤ |J|`?

Processors are `Fin m` (`i = 0, …, m - 1`), jobs `Fin |J|`. The open-shop schedule meeting the
deadline is `NoWaitFlowShopScheduling.IsOpenShopSchedule` from
`WantedExt.Complexity.NPComplete.NoWaitFlowShopSchedulingWanted`, which states Garey and
Johnson's definition verbatim: each `σ_i` is a one-processor schedule in the sense of [SS1] (a
one-to-one function with `σ_i(j) > σ_i(k)` implying `σ_i(j) ≥ σ_i(k) + l(t_i[k])`), the intervals
`[σ_i(j), σ_i(j) + l(t_i[j]))` of each job are pairwise disjoint (`Set.Ico`), and every task
ends by `D`. The instance type and the well-formedness condition (`0 < m`, every job has `m`
tasks, `0 < D`) are that module's as well (`NoWaitFlowShopScheduling.WellFormed`). Binary
encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of processors `m`, one list of task lengths
`(l(t_1[j]), …, l(t_m[j]))` per job `j`, and the deadline `D` (the instance type of
`NoWaitFlowShopSchedulingWanted`). -/
abbrev OpenShopSchedulingInstance := NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance

/-- Some open-shop schedule `σ p j` (start of job `j`'s task on processor `p`) meets the
deadline: `NoWaitFlowShopScheduling.IsOpenShopSchedule`, i.e., every `σ p` is one-to-one,
`σ p k < σ p j` implies `σ p k + l(t_p[k]) ≤ σ p j`, the tasks of each job occupy pairwise
disjoint intervals, and every task ends by `D`. -/
def OpenShopSchedulingFeasible (i : OpenShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, NoWaitFlowShopScheduling.IsOpenShopSchedule i σ

open Classical in
/-- OPEN-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def openShopSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenShopSchedulingInstance) x with
  | some i => decide (NoWaitFlowShopScheduling.WellFormed i ∧ OpenShopSchedulingFeasible i)
  | none => false

/-- **OPEN-SHOP SCHEDULING is NP-complete.** Source: Garey and Johnson (1979), [SS14];
Gonzalez and Sahni (1976). -/
public theorem_wanted openShopScheduling_npComplete :
    openShopSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L openShopSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling
