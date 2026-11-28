/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE FLOW SHOP WITH RELEASE DATES (F2|r_j|C_max): definitions

Source:
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X;
recorded in E. L. Lawler, J. K. Lenstra, A. H. G. Rinnooy Kan and D. B. Shmoys, "Sequencing and
scheduling: algorithms and complexity" (1989/1993), and in P. Brucker and S. Knust, "Complexity
results for scheduling problems" (minimal NP-hard `F2|r_i|C_max`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineFlowShopReleaseDates

/-- An instance: the parent instance `(m, task lengths per job, D)` and the release dates. -/
abbrev TwoMachineFlowShopReleaseDatesInstance :=
  FlowShopScheduling.FlowShopSchedulingInstance × List ℕ

/-- Well-formedness: `m = 2`, every job has two tasks, and one release date per job. -/
def WellFormed (i : TwoMachineFlowShopReleaseDatesInstance) : Prop :=
  i.1.1 = 2 ∧ (∀ job ∈ i.1.2.1, job.length = 2) ∧ i.2.length = i.1.2.1.length

/-- Some flow-shop schedule `σ p j` meets the bound `D` and starts each job's first task no
earlier than its release date. -/
def TwoMachineFlowShopReleaseDatesFeasible (i : TwoMachineFlowShopReleaseDatesInstance) :
    Prop :=
  ∃ σ : Fin i.1.1 → Fin i.1.2.1.length → ℕ,
    (∀ p j, σ p j + FlowShopScheduling.len i.1 p j ≤ i.1.2.2) ∧
    (∀ p j k, j ≠ k → σ p j + FlowShopScheduling.len i.1 p j ≤ σ p k ∨
      σ p k + FlowShopScheduling.len i.1 p k ≤ σ p j) ∧
    (∀ (p : Fin i.1.1) (hp : p.1 + 1 < i.1.1) j,
      σ p j + FlowShopScheduling.len i.1 p j ≤ σ ⟨p.1 + 1, hp⟩ j) ∧
    ∀ (p : Fin i.1.1), p.1 = 0 → ∀ j : Fin i.1.2.1.length, i.2.getD j 0 ≤ σ p j

open Classical in
/-- TWO-MACHINE FLOW SHOP WITH RELEASE DATES (F2|r_j|C_max) as a decision
problem over bitstrings. -/
noncomputable def twoMachineFlowShopReleaseDatesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineFlowShopReleaseDatesInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineFlowShopReleaseDatesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineFlowShopReleaseDates
