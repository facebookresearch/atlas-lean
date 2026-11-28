/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# J2|p_ij=1|Σw_jT_j (two-machine unit-time job shop, total weighted tardiness): definitions

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
recorded in P. Brucker and S. Knust, "Complexity results for scheduling problems", table
"Job-shop problems without preemption" (minimal NP-hard in the strong sense).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitJobShopWeightedTardiness

/-- An instance: the parent instance (`m`, each job's tasks `(l(t), p(t))`, the bound `K`) and
one pair `(dⱼ, wⱼ)` (due date, weight) per job. -/
abbrev UnitJobShopWeightedTardinessInstance :=
  JobShopScheduling.JobShopSchedulingInstance × List (ℕ × ℕ)

/-- Well-formedness: `m = 2`, every job is a nonempty chain of unit tasks on processors `1`, `2`
with consecutive tasks on different processors, and one pair per job. -/
def WellFormed (i : UnitJobShopWeightedTardinessInstance) : Prop :=
  i.1.1 = 2 ∧ (∀ job ∈ i.1.2.1, job ≠ []) ∧
    (∀ job ∈ i.1.2.1, ∀ t ∈ job, t.1 = 1 ∧ 1 ≤ t.2 ∧ t.2 ≤ 2) ∧
    (∀ job ∈ i.1.2.1, job.IsChain fun t t' => t.2 ≠ t'.2) ∧ i.2.length = i.1.2.1.length

/-- Some job-shop schedule `σ` of the unit tasks has `Σⱼ wⱼ max(0, Cⱼ - dⱼ) ≤ K` (natural
subtraction `C j - dⱼ` is `max(0, C j - dⱼ)`), where `C j` is the end of the last task of job `j`.
-/
def UnitJobShopWeightedTardinessFeasible (i : UnitJobShopWeightedTardinessInstance) :
    Prop :=
  ∃ σ : JobShopScheduling.Task i.1 → ℕ,
    (∀ t t', JobShopScheduling.taskProcessor i.1 t = JobShopScheduling.taskProcessor i.1 t' →
      σ t = σ t' → t = t') ∧
    (∀ t t', JobShopScheduling.taskProcessor i.1 t = JobShopScheduling.taskProcessor i.1 t' →
      σ t' < σ t → σ t' + JobShopScheduling.taskLength i.1 t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.1.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + JobShopScheduling.taskLength i.1 ⟨j, k⟩ ≤ σ ⟨j, k'⟩) ∧
    ∃ C : Fin i.1.2.1.length → ℕ,
      (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
        C j = σ ⟨j, k⟩ + JobShopScheduling.taskLength i.1 ⟨j, k⟩) ∧
      ∑ j : Fin i.1.2.1.length, (i.2.getD j (0, 0)).2 * (C j - (i.2.getD j (0, 0)).1) ≤ i.1.2.2

open Classical in
/-- J2|p_ij=1|Σw_jT_j as a decision
problem over bitstrings. -/
noncomputable def unitJobShopWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitJobShopWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ UnitJobShopWeightedTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitJobShopWeightedTardiness
