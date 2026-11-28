/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS AND UNIT TIMES, number of late jobs
(`PMPM2|chains; pᵢ = 1|ΣUᵢ`): definitions

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 10 (multi-purpose machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Parallel machine problems with
multi-purpose machines", which lists `PMPM2|chains;p_i=1|ΣU_i` as minimal NP-hard in the strong
sense ("Single-machine problem");
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 1 (the single-machine problem `1|chains;p_j=1|ΣU_j`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsMakespanDefs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsLateJobs

open MultiPurposeJobShopThreeJobs (Operation opLength IsMPMJobShopSchedule)
open MultipurposeParallelTwoMachinesUnitChainsMakespan
  (MultipurposeParallelTwoMachinesUnitChainsMakespanInstance)
open UnitFlowShopPrecedenceMakespan (Prec)

/-- An instance: a `PMPM2|chains; pᵢ = 1|C_max` instance (whose bound is the bound `K` on the number
of late jobs) and the due dates `dᵢ`, job `j` having the `j`-th listed due date. -/
abbrev MultipurposeParallelTwoMachinesUnitChainsLateJobsInstance :=
  MultipurposeParallelTwoMachinesUnitChainsMakespanInstance × List ℕ

/-- Well-formedness of an instance: a well-formed `PMPM2|chains; pᵢ = 1|C_max` instance and one due
date per job. -/
def WellFormed (i : MultipurposeParallelTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  MultipurposeParallelTwoMachinesUnitChainsMakespan.WellFormed i.1 ∧
    i.2.length = i.1.1.2.1.length

/-- Some MPM schedule of the jobs obeys the precedence arcs and has at most `K` late jobs: jobs
whose operation `t` completes after the due date of its job, `d < σ t + p_t`. -/
def MultipurposeParallelTwoMachinesUnitChainsLateJobsFeasible
    (i : MultipurposeParallelTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  ∃ a σ : Operation i.1.1 → ℕ, IsMPMJobShopSchedule i.1.1 a σ ∧
    (∀ t t' : Operation i.1.1, Prec i.1.2 t.1 t'.1 → σ t + opLength i.1.1 t ≤ σ t') ∧
    (Finset.univ.filter fun t : Operation i.1.1 =>
      i.2.getD t.1 0 < σ t + opLength i.1.1 t).card ≤ i.1.1.2.2

open Classical in
/-- `PMPM2|chains; pᵢ = 1|ΣUᵢ` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesUnitChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesUnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelTwoMachinesUnitChainsLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsLateJobs
