/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP `O2|p_ij=1;chains;no-wait|ΣU_i`: definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1; recorded as strongly NP-hard (a minimal NP-hard problem) in P.
Brucker and S. Knust, *Complexity results for scheduling problems*, class "Open-shop problems with
nowait" (University of Osnabrück, http://www2.informatik.uni-osnabrueck.de/knust/class/), problem
`O2|p_ij=1;chains;no-wait|ΣU_i`, credited to Timkovsky (2003).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.O2UnitChainsNoWaitLateJobs

open F3UnitChainsLateJobs (F3UnitChainsLateJobsInstance WellFormed)
open UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-- Some two-machine unit-time open-shop schedule `σ` obeying the chain arcs
(`IsUnitOpenShopSchedule 2`) in which every job runs its two operations back to back has at most `K`
late jobs: jobs `j` whose completion time `C_j = max (σ 0 j) (σ 1 j) + 1` exceeds the due date
`d_j`. -/
def O2UnitChainsNoWaitLateJobsFeasible (i : F3UnitChainsLateJobsInstance) : Prop :=
  ∃ σ : Fin 2 → Fin i.1.length → ℕ, IsUnitOpenShopSchedule 2 i.1.length i.2.1 σ ∧
    (∀ j, σ 0 j + 1 = σ 1 j ∨ σ 1 j + 1 = σ 0 j) ∧
    (Finset.univ.filter fun j : Fin i.1.length =>
      i.1.get j < max (σ 0 j) (σ 1 j) + 1).card ≤ i.2.2

open Classical in
/-- `O2|p_ij=1;chains;no-wait|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def o2UnitChainsNoWaitLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ O2UnitChainsNoWaitLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.O2UnitChainsNoWaitLateJobs
