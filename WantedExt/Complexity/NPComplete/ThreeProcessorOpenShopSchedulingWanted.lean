/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR OPEN-SHOP SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING, comment:
remains NP-complete if `m = 3`;
T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time", Journal of the ACM 23
(1976), 665-679, doi:10.1145/321978.321985.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.OpenShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOpenShopScheduling

/-!
# THREE-PROCESSOR OPEN-SHOP SCHEDULING is NP-complete

INSTANCE: `m = 3` processors, a set `J` of jobs, each job `j ∈ J` consisting of 3 tasks
`t_1[j], t_2[j], t_3[j]` (with `t_i[j]` to be executed by processor `i`), a length
`l(t) ∈ ℤ₀⁺` for each such task `t`, and an overall deadline `D ∈ ℤ⁺`. QUESTION: is there an
open-shop schedule for `J` that meets the deadline, i.e., a collection of one-processor schedules
`σ_i : J → ℤ₀⁺`, `1 ≤ i ≤ 3`, such that `σ_i(j) > σ_i(k)` implies `σ_i(j) ≥ σ_i(k) + l(t_i[k])`,
such that for each `j ∈ J` the intervals `[σ_i(j), σ_i(j) + l(t_i[j]))` are all disjoint, and
such that `σ_i(j) + l(t_i[j]) ≤ D` for `1 ≤ i ≤ 3`, `1 ≤ j ≤ |J|`?

This is the restriction of OPEN-SHOP SCHEDULING
(`WantedExt.Complexity.NPComplete.OpenShopSchedulingWanted`) to `m = 3`. The instance type, the
parent well-formedness condition and the question are that module's
(`OpenShopScheduling.OpenShopSchedulingInstance`, `NoWaitFlowShopScheduling.WellFormed`,
`OpenShopScheduling.OpenShopSchedulingFeasible`); the restriction is added to `WellFormed`.
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

/-- Well-formedness of an instance: it is a well-formed OPEN-SHOP SCHEDULING instance (`0 < m`,
every job has `m` tasks, `0 < D`) with `m = 3` processors. -/
def WellFormed (i : OpenShopScheduling.OpenShopSchedulingInstance) : Prop :=
  NoWaitFlowShopScheduling.WellFormed i ∧ i.1 = 3

open Classical in
/-- THREE-PROCESSOR OPEN-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def threeProcessorOpenShopSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenShopScheduling.OpenShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ OpenShopScheduling.OpenShopSchedulingFeasible i)
  | none => false

/-- **THREE-PROCESSOR OPEN-SHOP SCHEDULING is NP-complete.** Source: Garey and Johnson (1979),
[SS14], comment; Gonzalez and Sahni (1976). -/
public theorem_wanted threeProcessorOpenShopScheduling_npComplete :
    threeProcessorOpenShopSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorOpenShopSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOpenShopScheduling
