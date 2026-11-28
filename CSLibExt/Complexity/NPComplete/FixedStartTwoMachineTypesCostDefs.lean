/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING TO MINIMIZE MACHINE COST (two machine types, fixed start times): definitions

Source:
K. Nakajima, S. L. Hakimi and J. K. Lenstra, "Complexity results for scheduling tasks in fixed
intervals on two types of machines", SIAM Journal on Computing 11 (1982), 512-520,
doi:10.1137/0211040, Theorem 2 ("The FST problem is NP-hard in the strong sense").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fin.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedStartTwoMachineTypesCost

/-- An instance: the tasks `(rⱼ, pⱼ, qⱼ)` (release date, slow and fast processing time), the slow
machine cost `Cˢ`, the fast machine cost `Cᶠ`, and the bound `B`. -/
abbrev FixedStartTwoMachineTypesCostInstance := List (ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ

/-- Well-formedness of an instance: every task has `0 < qⱼ < pⱼ`, and `0 < Cˢ < Cᶠ`. -/
def WellFormed (i : FixedStartTwoMachineTypesCostInstance) : Prop :=
  (∀ t ∈ i.1, 0 < t.2.2 ∧ t.2.2 < t.2.1) ∧ 0 < i.2.1 ∧ i.2.1 < i.2.2.1

/-- The release date of task `j`. -/
def release (i : FixedStartTwoMachineTypesCostInstance) (j : Fin i.1.length) : ℕ :=
  (i.1.get j).1

/-- The processing time of task `j` on a machine of the given type: `pⱼ` on a slow machine
(`Sum.inl`), `qⱼ` on a fast machine (`Sum.inr`). -/
def duration {ms mf : ℕ} (i : FixedStartTwoMachineTypesCostInstance) (j : Fin i.1.length) :
    Fin ms ⊕ Fin mf → ℕ
  | Sum.inl _ => (i.1.get j).2.1
  | Sum.inr _ => (i.1.get j).2.2

/-- A feasible schedule of total cost at most `B`: `mˢ` slow and `mᶠ` fast machines with
`mˢ Cˢ + mᶠ Cᶠ ≤ B`, and an assignment `σ` of tasks to machines such that two distinct tasks on
the same machine do not overlap, each task starting at its release date. -/
def FixedStartTwoMachineTypesCostFeasible (i : FixedStartTwoMachineTypesCostInstance) : Prop :=
  ∃ (ms mf : ℕ) (σ : Fin i.1.length → Fin ms ⊕ Fin mf), ms * i.2.1 + mf * i.2.2.1 ≤ i.2.2.2 ∧
    ∀ j k, j ≠ k → σ j = σ k →
      release i j + duration i j (σ j) ≤ release i k ∨
        release i k + duration i k (σ k) ≤ release i j

open Classical in
/-- SCHEDULING TO MINIMIZE MACHINE COST (two machine types, fixed start times) as a decision
problem over bitstrings. -/
noncomputable def fixedStartTwoMachineTypesCostDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FixedStartTwoMachineTypesCostInstance) x with
  | some i => decide (WellFormed i ∧ FixedStartTwoMachineTypesCostFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FixedStartTwoMachineTypesCost
