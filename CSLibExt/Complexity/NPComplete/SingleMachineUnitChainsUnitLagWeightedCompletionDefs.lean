/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE SCHEDULING WITH UNIT TIME LAGS `1|chains(1);p_i=1|Σw_iC_i`: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Single machine
problems with non-negative time-lags" (University of Osnabrück, last updated 2003), minimal
NP-hard problem (strong sense) `1|chains(1);p_i=1|Σw_iC_i`, citing
V. S. Tanaev, Y. N. Sotskov and V. A. Strusevich, *Scheduling Theory. Multi-Stage Systems*,
Mathematics and its Applications 285, Kluwer Academic Publishers, Dordrecht (1994),
doi:10.1007/978-94-011-1192-8.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs
public import CSLibExt.Complexity.NPComplete.SingleMachineChainsTimeLagMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleMachineUnitChainsUnitLagWeightedCompletion

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)
open SingleMachineChainsTimeLagMakespan (SingleMachineChainsTimeLagMakespanInstance)

/-- The weight `w_j` of job `j`: the `j`-th listed number. -/
def weight (i : SingleMachineChainsTimeLagMakespanInstance) (j : ℕ) : ℕ := i.1.getD j 0

/-- Well-formedness of an instance: well-formed for `1|chains(l)|C_max` (the chains consist of
job indices, and no job occurs twice), and the time lag is `1`. -/
def WellFormed (i : SingleMachineChainsTimeLagMakespanInstance) : Prop :=
  SingleMachineChainsTimeLagMakespan.WellFormed i ∧ i.2.2.1 = 1

/-- Some start times `S` never run two unit jobs at once, start each job in a chain at least the
lag `1` after its immediate predecessor completes, and have total weighted completion time
`Σ_j w_j (S j + 1)` at most `K`. -/
def SingleMachineUnitChainsUnitLagWeightedCompletionFeasible
    (i : SingleMachineChainsTimeLagMakespanInstance) : Prop :=
  ∃ S : ℕ → ℕ,
    IsOneProcessorSchedule (fun _ : Fin i.1.length => 1) (fun j => S j) ∧
    (∀ c ∈ i.2.1, ∀ k, k + 1 < c.length →
      S (c.getD k 0) + 1 + i.2.2.1 ≤ S (c.getD (k + 1) 0)) ∧
    ∑ j ∈ Finset.range i.1.length, weight i j * (S j + 1) ≤ i.2.2.2

open Classical in
/-- `1|chains(1);p_i=1|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def singleMachineUnitChainsUnitLagWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleMachineChainsTimeLagMakespanInstance) x with
  | some i => decide (WellFormed i ∧ SingleMachineUnitChainsUnitLagWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SingleMachineUnitChainsUnitLagWeightedCompletion
