/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|ΣU_i`: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `o_now` (open-shop problems with
no-wait), entry `O3|p_ij=1;chains;no-wait|ΣU_i` (minimal NP-hard in the strong sense, citing
Timkovsky 2003);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (only the abstract and introduction were available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.O3UnitChainsNoWaitLateJobs

open F3UnitChainsLateJobs (F3UnitChainsLateJobsInstance WellFormed)
open UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-- `σ k j` (start of job `j`'s unit operation on machine `k`) is a no-wait unit-time open-shop
schedule on `m` machines for the precedence arcs `A`, job `j` starting at `S j`: `σ` is a
unit-time open-shop schedule (`UnitOpenShopOutTreeMaxLateness.IsUnitOpenShopSchedule`), and every
operation of job `j` starts in `[S j, S j + m)`, so that the `m` operations of the job run back to
back from `S j` on. -/
def IsNoWaitSchedule (m n : ℕ) (A : List (ℕ × ℕ)) (S : Fin n → ℕ) (σ : Fin m → Fin n → ℕ) :
    Prop :=
  IsUnitOpenShopSchedule m n A σ ∧ ∀ k j, S j ≤ σ k j ∧ σ k j < S j + m

/-- Some no-wait schedule has at most `K` late jobs: jobs `j` with completion time
`C_j = S j + 3` greater than the due date `d_j`. -/
def O3UnitChainsNoWaitLateJobsFeasible (i : F3UnitChainsLateJobsInstance) : Prop :=
  ∃ (S : Fin i.1.length → ℕ) (σ : Fin 3 → Fin i.1.length → ℕ),
    IsNoWaitSchedule 3 i.1.length i.2.1 S σ ∧
      (Finset.univ.filter fun j : Fin i.1.length => i.1.get j < S j + 3).card ≤ i.2.2

open Classical in
/-- `O3|p_ij=1;chains;no-wait|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def o3UnitChainsNoWaitLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ O3UnitChainsNoWaitLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.O3UnitChainsNoWaitLateJobs
