/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP `O3|p_ij=1;chains|ΣU_i`: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `o_nop` (open shop problems without
preemption), entry `O3|p_ij=1;chains|ΣU_i` (minimal NP-hard in the strong sense, citing
Timkovsky 2003);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (abstract only; the full text was not available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanDefs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.O3UnitChainsLateJobs

open F3UnitChainsLateJobs (F3UnitChainsLateJobsInstance WellFormed)
open UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)
open MultipurposeFlowShopPrecedenceMakespan (completionTime)

/-- Some unit-time three-machine open-shop schedule obeying the chain arcs has at most `K` late
jobs: jobs `j` whose completion time `C_j` (the latest `σ k j + 1`) exceeds the due date `d_j`. -/
def O3UnitChainsLateJobsFeasible (i : F3UnitChainsLateJobsInstance) : Prop :=
  ∃ σ : Fin 3 → Fin i.1.length → ℕ, IsUnitOpenShopSchedule 3 i.1.length i.2.1 σ ∧
    (Finset.univ.filter fun j : Fin i.1.length =>
      i.1.get j < completionTime (fun _ _ => 1) (fun j k => σ k j) j).card ≤ i.2.2

open Classical in
/-- `O3|p_ij=1;chains|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def o3UnitChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ O3UnitChainsLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.O3UnitChainsLateJobs
