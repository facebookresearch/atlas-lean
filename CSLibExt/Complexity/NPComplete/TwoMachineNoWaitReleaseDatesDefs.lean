/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE NO-WAIT FLOW SHOP WITH RELEASE DATES (F2|r_j;no-wait|C_max): definitions

Source:
H. Röck, "Some new results in flow shop scheduling", Zeitschrift für Operations Research 28
(1984), 1-16, doi:10.1007/BF01919082; recorded in P. Brucker and S. Knust, "Complexity results
for scheduling problems" (minimal NP-hard `F2|r_i;no-wait|C_max`, Röck 1984) and in E. L. Lawler,
J. K. Lenstra, A. H. G. Rinnooy Kan and D. B. Shmoys, "Sequencing and scheduling: algorithms and
complexity" (1989/1993) (`F2|no wait|L_max` strongly NP-hard, Röck 1984).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineNoWaitReleaseDates

/-- An instance: the parent instance `(m, task lengths per job, D)` and the release dates. -/
abbrev TwoMachineNoWaitReleaseDatesInstance :=
  FlowShopScheduling.FlowShopSchedulingInstance × List ℕ

/-- Well-formedness: `m = 2`, every job has two tasks, and one release date per job. -/
def WellFormed (i : TwoMachineNoWaitReleaseDatesInstance) : Prop :=
  i.1.1 = 2 ∧ (∀ job ∈ i.1.2.1, job.length = 2) ∧ i.2.length = i.1.2.1.length

/-- Some flow-shop schedule `σ p j` meets the bound `D`, starts each job's first task no earlier
than its release date, and starts each later task exactly when the previous task of the job
ends. -/
def TwoMachineNoWaitReleaseDatesFeasible (i : TwoMachineNoWaitReleaseDatesInstance) :
    Prop :=
  ∃ σ : Fin i.1.1 → Fin i.1.2.1.length → ℕ,
    (∀ p j, σ p j + FlowShopScheduling.len i.1 p j ≤ i.1.2.2) ∧
    (∀ p j k, j ≠ k → σ p j + FlowShopScheduling.len i.1 p j ≤ σ p k ∨
      σ p k + FlowShopScheduling.len i.1 p k ≤ σ p j) ∧
    (∀ (p : Fin i.1.1) (hp : p.1 + 1 < i.1.1) j,
      σ ⟨p.1 + 1, hp⟩ j = σ p j + FlowShopScheduling.len i.1 p j) ∧
    ∀ (p : Fin i.1.1), p.1 = 0 → ∀ j : Fin i.1.2.1.length, i.2.getD j 0 ≤ σ p j

open Classical in
/-- TWO-MACHINE NO-WAIT FLOW SHOP WITH RELEASE DATES (F2|r_j;no-wait|C_max) as a decision
problem over bitstrings. -/
noncomputable def twoMachineNoWaitReleaseDatesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineNoWaitReleaseDatesInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineNoWaitReleaseDatesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineNoWaitReleaseDates
