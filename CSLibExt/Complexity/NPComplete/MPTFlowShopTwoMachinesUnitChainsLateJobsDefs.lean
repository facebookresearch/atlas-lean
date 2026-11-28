/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP FMPT2|chains;p_ij=1|ΣU_i: definitions

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the MPT flow-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT2|chains;p_ij=1|ΣU_i` as minimal NP-hard in the strong sense
("Single-machine problem");
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 1 (the single-machine problem `1|chains;p_j=1|ΣU_j`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespanDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsLateJobs

open MPMOpenShopTwoMachinesUnitChainsLateJobs (MPMOpenShopTwoMachinesUnitChainsLateJobsInstance)
open F3UnitChainsLateJobs (ChainsWellFormed)
open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTPrecedenceSchedule)

/-- Well-formedness: a two-machine MPT environment (`StagesWellFormed 2`), and chain arcs on the
jobs. -/
def WellFormed (i : MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  StagesWellFormed 2 i.1 ∧ ChainsWellFormed i.2.1.length i.2.2.1

/-- Some MPT flow-shop schedule of the unit-time jobs on the two machines obeying the chain arcs has
at most `K` late jobs (jobs `i` with `C_i > d_i`). -/
def MPTFlowShopTwoMachinesUnitChainsLateJobsFeasible
    (i : MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Fin i.1.length → ℕ,
    IsMPTPrecedenceSchedule i.1 i.2.2.1 σ ∧
      (Finset.univ.filter fun j : Fin i.2.1.length =>
        i.2.1.get j < completionTime (fun _ _ => 1) σ j).card ≤ i.2.2.2

open Classical in
/-- `FMPT2|chains;p_ij=1|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def mptFlowShopTwoMachinesUnitChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ MPTFlowShopTwoMachinesUnitChainsLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsLateJobs
