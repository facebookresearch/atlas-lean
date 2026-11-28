/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH UNIT-TIME CHAINS (PMPM2|chains;p_i=1|Σw_iC_i):
definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8 (the full
texts of both papers were not available);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Parallel machine
problems without preemption" (`P2|p_i=1;chains|Σw_iC_i`, minimal NP-hard in the strong sense,
credited to Timkovsky (2003)) and class "Multipurpose machine problems"
(`PMPM2|chains;p_i=1|Σw_iC_i`, minimal NP-hard in the strong sense, credited to Timkovsky
(1998));
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMParallelTwoMachinesUnitChainsWeightedCompletion

open MultiPurposeJobShopThreeJobs (Operation opLength IsMPMJobShopSchedule)
open UnitFlowShopPrecedenceMakespan (Prec)
open MultipurposeParallelTwoMachinesUnitChainsMakespan
  (MultipurposeParallelTwoMachinesUnitChainsMakespanInstance)

/-- An instance: a `PMPM2|chains; p_i=1|C_max` instance (the MPM job-shop instance, whose bound
component is `K`, and the precedence arcs) and the weights, job `j` having the `j`-th listed
weight `w_j`. -/
abbrev MPMParallelTwoMachinesUnitChainsWeightedCompletionInstance :=
  MultipurposeParallelTwoMachinesUnitChainsMakespanInstance × List ℕ

/-- The weight `w_j` of job `j`. -/
def weight (i : MPMParallelTwoMachinesUnitChainsWeightedCompletionInstance)
    (j : Fin i.1.1.2.1.length) : ℕ :=
  i.2.getD j 0

/-- Well-formedness of an instance: a well-formed `PMPM2|chains; p_i=1|C_max` instance (two
machines, nonempty machine sets in `{1, 2}`, unit single-operation jobs, acyclic arcs naming jobs
that form chains) and one weight per job. -/
def WellFormed (i : MPMParallelTwoMachinesUnitChainsWeightedCompletionInstance) : Prop :=
  MultipurposeParallelTwoMachinesUnitChainsMakespan.WellFormed i.1 ∧
    i.2.length = i.1.1.2.1.length

/-- Some MPM schedule of the jobs obeys the precedence arcs and has total weighted completion
time at most `K`: the sum, over the operations `t` (one per job), of `w_j · (σ t + p_t)` for the
job `j` of `t`. -/
def MPMParallelTwoMachinesUnitChainsWeightedCompletionFeasible
    (i : MPMParallelTwoMachinesUnitChainsWeightedCompletionInstance) : Prop :=
  ∃ a σ : Operation i.1.1 → ℕ, IsMPMJobShopSchedule i.1.1 a σ ∧
    (∀ t t' : Operation i.1.1, Prec i.1.2 t.1 t'.1 → σ t + opLength i.1.1 t ≤ σ t') ∧
    (∑ t : Operation i.1.1, weight i t.1 * (σ t + opLength i.1.1 t)) ≤ i.1.1.2.2

open Classical in
/-- `PMPM2|chains; p_i=1|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def mpmParallelTwoMachinesUnitChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMParallelTwoMachinesUnitChainsWeightedCompletionInstance) x with
  | some i =>
    decide (WellFormed i ∧ MPMParallelTwoMachinesUnitChainsWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MPMParallelTwoMachinesUnitChainsWeightedCompletion
