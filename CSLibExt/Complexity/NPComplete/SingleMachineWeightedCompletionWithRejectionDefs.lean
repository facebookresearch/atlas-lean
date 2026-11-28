/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE SCHEDULING WITH REJECTION (weighted completion time): definitions

Source:
D. W. Engels, D. R. Karger, S. G. Kolliopoulos, S. Sengupta, R. N. Uma and J. Wein,
"Techniques for scheduling with rejection", Journal of Algorithms 49(1) (2003), 175-191,
doi:10.1016/S0196-6774(03)00078-6 (conference version: ESA 1998, LNCS 1461, 490-501,
doi:10.1007/3-540-68530-8_41).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Sort
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleMachineWeightedCompletionWithRejection

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: the jobs as `(p_j, w_j, e_j)`, and the bound `K`. -/
abbrev SingleMachineWeightedCompletionWithRejectionInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- The jobs of the instance. -/
abbrev Job (i : SingleMachineWeightedCompletionWithRejectionInstance) : Type := Fin i.1.length

/-- The processing time `p_j` of job `j`. -/
def processingTime (i : SingleMachineWeightedCompletionWithRejectionInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The weight `w_j` of job `j`. -/
def weight (i : SingleMachineWeightedCompletionWithRejectionInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.1

/-- The rejection penalty `e_j` of job `j`. -/
def penalty (i : SingleMachineWeightedCompletionWithRejectionInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Well-formedness of an instance: every processing time is positive. -/
def WellFormed (i : SingleMachineWeightedCompletionWithRejectionInstance) : Prop :=
  ∀ x ∈ i.1, 0 < x.1

/-- Some set `S` of accepted jobs (the others are rejected) and start times `σ` that form a
one-processor schedule of the accepted jobs give `∑_{j ∈ S} w_j (σ_j + p_j) + ∑_{j ∉ S} e_j`
at most `K`. -/
def SingleMachineWeightedCompletionWithRejectionFeasible
    (i : SingleMachineWeightedCompletionWithRejectionInstance) : Prop :=
  ∃ S : Finset (Job i), ∃ σ : Job i → ℕ,
    IsOneProcessorSchedule (fun k => processingTime i (S.orderEmbOfFin rfl k))
      (fun k => σ (S.orderEmbOfFin rfl k)) ∧
    ∑ j ∈ S, weight i j * (σ j + processingTime i j) + ∑ j ∈ Sᶜ, penalty i j ≤ i.2

open Classical in
/-- SINGLE-MACHINE SCHEDULING WITH REJECTION as a decision problem over bitstrings. -/
noncomputable def singleMachineWeightedCompletionWithRejectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleMachineWeightedCompletionWithRejectionInstance) x with
  | some i => decide (WellFormed i ∧ SingleMachineWeightedCompletionWithRejectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SingleMachineWeightedCompletionWithRejection
