/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR OPEN-SHOP MEAN FLOW TIME (O2||ΣC_i) is NP-complete

Source:
J. O. Achugbue and F. Y. Chin, "Scheduling the open shop to minimize mean flow time", SIAM
Journal on Computing 11 (1982), 709-720, doi:10.1137/0211058;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `o_nop` (open-shop problems without preemption), Universität Osnabrück (last update 2006).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import WantedExt.Complexity.NPComplete.OpenShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopMeanFlowTime

open OpenShopScheduling (OpenShopSchedulingInstance)
open NoWaitFlowShopScheduling (IsOpenShopSchedule taskLength)

/-!
# TWO-PROCESSOR OPEN-SHOP MEAN FLOW TIME (O2||ΣC_i) is NP-complete

INSTANCE: `m = 2` processors, a nonempty set `J` of jobs, each job `j ∈ J` consisting of two tasks
`t₁[j], t₂[j]` (task `tᵢ[j]` runs on processor `i`), a length `l(t) ∈ ℤ₀⁺` for each such task,
and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a nonpreemptive open-shop schedule for `J` (each
processor runs one task at a time, the two tasks of a job run in either order but not at the
same time) whose total completion time `∑_j C_j` is at most `K`, where `C_j` is the time at
which the last task of job `j` completes?

In the three-field notation this is `O2||∑ C_i`; minimizing the mean flow time `∑_j C_j / |J|`
is the same problem. Achugbue and Chin (1982) prove it NP-complete even if the input length is
measured by the sum of the task lengths (NP-complete in the strong sense); Brucker and Knust's
classification lists it as minimal strongly NP-hard, citing them.

The instance type, the task lengths `taskLength` and the open-shop schedule `IsOpenShopSchedule` are
those of OPEN-SHOP SCHEDULING ([SS14], `OpenShopSchedulingWanted`, defined in
`NoWaitFlowShopSchedulingWanted`): one-processor schedules `σ_i` in the sense of [SS1] (one-to-one,
and `σ_i(j) > σ_i(k)` implies `σ_i(j) ≥ σ_i(k) + l(tᵢ[k])`), the two tasks of each job in disjoint
intervals, and every task ending by the last component of the instance, which here is the bound `K`
(the deadline `D` of [SS14] is replaced by the bound on the sum). That deadline condition is implied
by the sum bound, since every task ends by the completion time of its job and every completion time
is at most the sum, so it does not change the answer. `WellFormed` asks for `m = 2`, two tasks per
job and at least one job (the source schedules an `n`-job open shop, and the mean flow time divides
by `|J|`); it does not ask for `K > 0`, the condition `D ∈ ℤ⁺` of [SS14], since the source puts no
condition on the bound. As in [SS1], tasks of length `0` count: the one-processor schedules are
one-to-one on them too, as in the two-processor flow-shop mean flow time problem
(`TwoProcessorFlowShopMeanFlowTimeWanted`). The completion time of job `j` is `C_j = max_i (σ_i(j) +
l(tᵢ[j]))`. Processors are `Fin m` (`i = 0, 1`), jobs `Fin |J|`. Binary encoding of all numbers.
Membership in NP: every start time is at most `K`, so the start times form a certificate of
polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: two processors, every job consists of two tasks, and there
is at least one job. -/
def WellFormed (i : OpenShopSchedulingInstance) : Prop :=
  i.1 = 2 ∧ (∀ job ∈ i.2.1, job.length = i.1) ∧ 0 < i.2.1.length

/-- Some open-shop schedule `σ p j` (start of job `j`'s task on processor `p`), with every task
ending by `K`, has total completion time `∑_j max_p (σ p j + l(t_p[j]))` at most `K`. -/
def TwoProcessorOpenShopMeanFlowTimeFeasible (i : OpenShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsOpenShopSchedule i σ ∧
    ∑ j, Finset.univ.sup (fun p => σ p j + taskLength i p j) ≤ i.2.2

open Classical in
/-- TWO-PROCESSOR OPEN-SHOP MEAN FLOW TIME `O2||∑ C_i` as a decision problem over
bitstrings. -/
noncomputable def twoProcessorOpenShopMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorOpenShopMeanFlowTimeFeasible i)
  | none => false

/-- **TWO-PROCESSOR OPEN-SHOP MEAN FLOW TIME `O2||∑ C_i` is NP-complete.** Source: Achugbue
and Chin (1982); Brucker and Knust, scheduling classification, class `o_nop`. -/
public theorem_wanted twoProcessorOpenShopMeanFlowTime_npComplete :
    twoProcessorOpenShopMeanFlowTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorOpenShopMeanFlowTimeDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopMeanFlowTime
