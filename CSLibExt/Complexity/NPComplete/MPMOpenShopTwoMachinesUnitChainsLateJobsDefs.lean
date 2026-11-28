/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
# MPM OPEN SHOP OMPM2|chains;p_ij=1|ΣU_i: definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1; P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007),
doi:10.1007/978-3-540-69516-5, Chapter 10 (the MPM open-shop model); P. Brucker and S. Knust,
*Complexity results for scheduling problems*, http://www2.informatik.uni-osnabrueck.de/knust/class/,
class "Shop problems with multipurpose machines", which lists `OMPM2|chains;p_ij=1|ΣU_i` as minimal
NP-hard in the strong sense, citing Timkovsky (2003), and class "Open-shop problems without
preemption", which lists the special case `O2|p_ij=1;chains|ΣU_i` as minimal NP-hard in the strong
sense, citing Timkovsky (2003).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsLateJobs

open F3UnitChainsLateJobs (ChainsWellFormed)
open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)

/-- An instance `(μ, d, chains, K)`: the stage machine sets `[μ_1, …, μ_r]` (lists of machine
indices), the due dates `d_i` of the jobs `0, …, n - 1` (`n` is the length of the list), the chain
arcs `(i, k)` (job `i` immediately precedes job `k`), and the bound `K`. -/
abbrev MPMOpenShopTwoMachinesUnitChainsLateJobsInstance := List (List ℕ) × List ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness: a two-machine MPM environment with nonempty machine sets, and chain arcs on the
jobs. -/
def WellFormed (i : MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  StagesWellFormed 2 i.1 ∧ (∀ M ∈ i.1, M ≠ []) ∧ ChainsWellFormed i.2.1.length i.2.2.1

/-- Some MPM open-shop schedule of the unit-time jobs on the two machines obeying the chain arcs has
at most `K` late jobs (jobs `i` with `C_i > d_i`). -/
def MPMOpenShopTwoMachinesUnitChainsLateJobsFeasible
    (i : MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Fin i.1.length → ℕ, ∃ a : Fin i.2.1.length → Fin i.1.length → Fin 2,
    IsMPMOpenShopPrecedenceSchedule 2 i.1 i.2.2.1 σ a ∧
      (Finset.univ.filter fun j : Fin i.2.1.length =>
        i.2.1.get j < completionTime (fun _ _ => 1) σ j).card ≤ i.2.2.2

open Classical in
/-- `OMPM2|chains;p_ij=1|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def mpmOpenShopTwoMachinesUnitChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ MPMOpenShopTwoMachinesUnitChainsLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsLateJobs
