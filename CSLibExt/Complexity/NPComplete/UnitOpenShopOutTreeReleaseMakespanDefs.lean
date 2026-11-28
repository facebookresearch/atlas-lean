/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O|p_ij=1;outtree;r_i|Cmax: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Open-shop problems without preemption", minimal NP-hard entry
`O | p_ij = 1; outtree; r_i | C_max`, NP-hard in the strong sense, credited to Timkovsky (2003));
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLatenessDefs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeReleaseMakespan

open MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-- An instance `(m, J, A, K)`: the number of machines `m`, the jobs `J` (job `j` listed as its
processing times `(p_j1, …, p_jm)` and its release date `r_j`), the precedence arcs `A`
(`(i, j)`: job `i` precedes job `j`), and the bound `K`. -/
abbrev UnitOpenShopOutTreeReleaseMakespanInstance :=
  ℕ × List (List ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance `(m, J, A, K)`: well-formed for the unit-time out-tree flow
shop once the release dates are set aside (`m ≥ 1`, every job has `m` unit operations, the arcs
name jobs and are acyclic, and each job has at most one immediate predecessor), and there is at
least one job. -/
def WellFormed (i : UnitOpenShopOutTreeReleaseMakespanInstance) : Prop :=
  UnitFlowShopOutTreeMaxLateness.WellFormed
    (i.1, i.2.1.map (fun job => (job.1, (0, 0))), i.2.2.1, (0, 0)) ∧ i.2.1 ≠ []

/-- Some open-shop schedule starts no operation of a job before its release date and completes
every operation by time `K` (makespan `max_j C_j ≤ K`). -/
def UnitOpenShopOutTreeReleaseMakespanFeasible (i : UnitOpenShopOutTreeReleaseMakespanInstance) :
    Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsUnitOpenShopSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    (∀ k j, (i.2.1.get j).2 ≤ σ k j) ∧ ∀ k j, σ k j + 1 ≤ i.2.2.2

open Classical in
/-- OPEN SHOP O|p_ij=1;outtree;r_i|Cmax as a decision problem over bitstrings. -/
noncomputable def unitOpenShopOutTreeReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitOpenShopOutTreeReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopOutTreeReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeReleaseMakespan
