/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM2|chains|Cmax: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Shop problems with multipurpose machines" (`OMPM2|chains|C_max`, minimal NP-hard in the
strong sense, credited to V. S. Tanaev, Y. N. Sotskov, and V. A. Strusevich, *Scheduling Theory.
Multi-Stage Systems*, Kluwer (1994), doi:10.1007/978-94-011-1192-8, which was not available;
their two-machine open shop `O2|chains|C_max` is the case `μ_j = {M_j}`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesChainsMakespan

open F3UnitChainsLateJobs (ChainsWellFormed)
open MultipurposeFlowShopPrecedenceMakespan (Prec completionTime)
open MultipurposeFlowShopThreeJobs (Job Stage processingTime)
open MultipurposeOpenShopMakespan (MultipurposeOpenShopMakespanInstance)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-- An instance: an `OMPM||C_max` instance (the number `m` of machines, the stage machine sets,
one list of processing times per job, the bound `K`) and the chain arcs `(i, k)`. -/
abbrev MultipurposeOpenShopTwoMachinesChainsMakespanInstance :=
  MultipurposeOpenShopMakespanInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed `OMPM||C_max` instance with `m = 2` machines,
whose arcs form chains on the jobs. -/
def WellFormed (i : MultipurposeOpenShopTwoMachinesChainsMakespanInstance) : Prop :=
  MultipurposeOpenShopMakespan.WellFormed i.1 ∧ i.1.1 = 2 ∧
    ChainsWellFormed i.1.2.2.1.length i.2

/-- Some MPM open-shop schedule of the jobs respects the chains (if `J_i` immediately precedes
`J_k`, no operation of `k` starts before `C_i`) and has makespan at most `K`. -/
def MultipurposeOpenShopTwoMachinesChainsMakespanFeasible
    (i : MultipurposeOpenShopTwoMachinesChainsMakespanInstance) : Prop :=
  ∃ σ : Job i.1 → Stage i.1 → ℕ, ∃ a : Job i.1 → Stage i.1 → Fin i.1.1,
    IsMPMOpenShopSchedule i.1.1 i.1.2.1 (processingTime i.1) σ a ∧
      (∀ j k, Prec i.2 j k → ∀ s, completionTime (processingTime i.1) σ j ≤ σ k s) ∧
      ∀ j, completionTime (processingTime i.1) σ j ≤ i.1.2.2.2

open Classical in
/-- `OMPM2|chains|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopTwoMachinesChainsMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeOpenShopTwoMachinesChainsMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeOpenShopTwoMachinesChainsMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesChainsMakespan
