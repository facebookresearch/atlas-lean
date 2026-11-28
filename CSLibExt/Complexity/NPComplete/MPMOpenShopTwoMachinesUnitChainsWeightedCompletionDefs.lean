/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
# MPM OPEN SHOP OMPM2|chains;p_ij=1|Σw_iC_i: definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1; P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007),
doi:10.1007/978-3-540-69516-5, Chapter 10 (the MPM open-shop model); P. Brucker and S. Knust,
*Complexity results for scheduling problems*, http://www2.informatik.uni-osnabrueck.de/knust/class/,
class "Shop problems with multipurpose machines", which lists `OMPM2|chains;p_ij=1|Σw_iC_i` as
minimal NP-hard in the strong sense, citing Timkovsky (2003), and class "Open-shop problems without
preemption", which lists the special case `O2|p_ij=1;chains|Σw_iC_i` as minimal NP-hard in the
strong sense, citing Timkovsky (2003).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsWeightedCompletion

open F3UnitChainsLateJobs (ChainsWellFormed)
open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)

/-- An instance `(μ, w, chains, K)`: the stage machine sets `[μ_1, …, μ_r]` (lists of machine
indices), the weights `w_i` of the jobs `0, …, n - 1` (`n` is the length of the list), the chain
arcs `(i, k)` (job `i` immediately precedes job `k`), and the bound `K`. -/
abbrev MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance :=
  List (List ℕ) × List ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness: a two-machine MPM environment with nonempty machine sets, and chain arcs on the
jobs. -/
def WellFormed (i : MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance) : Prop :=
  StagesWellFormed 2 i.1 ∧ (∀ M ∈ i.1, M ≠ []) ∧ ChainsWellFormed i.2.1.length i.2.2.1

/-- Some MPM open-shop schedule of the unit-time jobs on the two machines obeying the chain arcs has
total weighted completion time `Σ_i w_i C_i ≤ K`. -/
def MPMOpenShopTwoMachinesUnitChainsWeightedCompletionFeasible
    (i : MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Fin i.1.length → ℕ, ∃ a : Fin i.2.1.length → Fin i.1.length → Fin 2,
    IsMPMOpenShopPrecedenceSchedule 2 i.1 i.2.2.1 σ a ∧
      ∑ j, i.2.1.get j * completionTime (fun _ _ => 1) σ j ≤ i.2.2.2

open Classical in
/-- `OMPM2|chains;p_ij=1|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def mpmOpenShopTwoMachinesUnitChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ MPMOpenShopTwoMachinesUnitChainsWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsWeightedCompletion
