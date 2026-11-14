/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR FLOW-SHOP MEAN FLOW TIME is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS15] FLOW-SHOP SCHEDULING, p. 241
(comment: with a bound `K` on the sum of the completion times in place of the deadline, the
problem is NP-complete in the strong sense even if `m = 2`);
M. R. Garey, D. S. Johnson and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129, doi:10.1287/moor.1.2.117.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.FlowShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopMeanFlowTime

/-!
# TWO-PROCESSOR FLOW-SHOP MEAN FLOW TIME is NP-complete

INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of `m = 2` tasks `t_1[j]`, `t_2[j]`
(task `t_i[j]` runs on processor `i`), a length `l(t) ∈ ℤ₀⁺` for each such task, and a bound
`K ∈ ℤ⁺`. QUESTION: is there a flow-shop schedule for `J` such that the sum, over all `j ∈ J`,
of `σ_m(j) + l(t_m[j])` is at most `K`?

This is FLOW-SHOP SCHEDULING ([SS15], `FlowShopSchedulingWanted`) with `m = 2` and the goal
of meeting the overall deadline replaced by a bound `K` on the sum of the jobs' completion
times (Garey and Johnson's comment to [SS15]; the mean flow time is that sum divided by `|J|`).
The instance type `FlowShopScheduling.FlowShopSchedulingInstance`, the task lengths
`FlowShopScheduling.len` and `FlowShopScheduling.WellFormed` are the parent's; the last
component of the instance is the bound `K ∈ ℤ⁺` in place of the deadline `D ∈ ℤ⁺`, and
`WellFormed` adds `m = 2`. The schedule conditions are the parent's (one task at a time on each
processor, each job's tasks in processor order) with the deadline condition replaced by the
bound on the sum of the completion times `σ p j + l(t_p[j])` on the last processor `p`
(`p + 1 = m`), plus the requirement of [SS1] that each one-processor schedule `σ_i` is
one-to-one: tasks of length `0` count, so without it several zero-length jobs could share a
start time and lower the sum. Processors are `Fin m` (`i = 0, 1`), jobs `Fin |J|`. Binary
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

/-- Well-formedness of an instance: the parent's (`0 < m`, every job has `m` tasks, `0 < K`)
and `m = 2`. -/
def WellFormed (i : FlowShopScheduling.FlowShopSchedulingInstance) : Prop :=
  FlowShopScheduling.WellFormed i ∧ i.1 = 2

/-- Some schedule `σ p j` (start of job `j`'s task on processor `p`) is one-to-one on each
processor, runs one task at a time on each processor and each job's tasks in processor order,
and the sum over all jobs of the completion times on the last processor is at most `K`. -/
def TwoProcessorFlowShopMeanFlowTimeFeasible
    (i : FlowShopScheduling.FlowShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ,
    (∀ p, Function.Injective (σ p)) ∧
    (∀ p j k, j ≠ k →
      σ p j + FlowShopScheduling.len i p j ≤ σ p k ∨
        σ p k + FlowShopScheduling.len i p k ≤ σ p j) ∧
    (∀ (p : Fin i.1) (hp : p.1 + 1 < i.1) j,
      σ p j + FlowShopScheduling.len i p j ≤ σ ⟨p.1 + 1, hp⟩ j) ∧
    ∀ p : Fin i.1, p.1 + 1 = i.1 → ∑ j, (σ p j + FlowShopScheduling.len i p j) ≤ i.2.2

open Classical in
/-- TWO-PROCESSOR FLOW-SHOP MEAN FLOW TIME as a decision problem over bitstrings. -/
noncomputable def twoProcessorFlowShopMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FlowShopScheduling.FlowShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorFlowShopMeanFlowTimeFeasible i)
  | none => false

/-- **TWO-PROCESSOR FLOW-SHOP MEAN FLOW TIME is NP-complete.** Source: Garey and Johnson
(1979), [SS15], comment; Garey, Johnson and Sethi (1976). -/
public theorem_wanted twoProcessorFlowShopMeanFlowTime_npComplete :
    twoProcessorFlowShopMeanFlowTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorFlowShopMeanFlowTimeDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopMeanFlowTime
