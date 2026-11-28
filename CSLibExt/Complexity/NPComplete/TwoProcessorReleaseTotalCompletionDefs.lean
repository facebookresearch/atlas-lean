/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH RELEASE DATES, TOTAL COMPLETION TIME `P2|r_i|ΣC_i`: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pqr_nop` (parallel machine
problems without preemption), entry `P2|r_i|ΣC_i` (minimal NP-hard in the strong sense,
justified by the single-machine problem);
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X (`1|r_j|ΣC_j` is NP-hard in the strong sense).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TotalCompletionTimeWithReleaseTimesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorReleaseTotalCompletion

open TotalCompletionTimeWithReleaseTimes (TotalCompletionTimeWithReleaseTimesInstance Task
  taskLength releaseTime)

/-- Some two-machine schedule (start times `σ`, machines `μ`) processes two different jobs on
the same machine in disjoint intervals, starts every job no earlier than its release date, and
has total completion time `∑_i (σ(i) + p_i)` at most `K`. -/
def TwoProcessorReleaseTotalCompletionFeasible (i : TotalCompletionTimeWithReleaseTimesInstance) :
    Prop :=
  ∃ (σ : Task i → ℕ) (μ : Task i → Fin 2),
    (∀ t t', t ≠ t' → μ t = μ t' →
      σ t + taskLength i t ≤ σ t' ∨ σ t' + taskLength i t' ≤ σ t) ∧
    (∀ t, releaseTime i t ≤ σ t) ∧
    ∑ t, (σ t + taskLength i t) ≤ i.2

open Classical in
/-- `P2|r_i|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def twoProcessorReleaseTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TotalCompletionTimeWithReleaseTimesInstance) x with
  | some i => decide (TotalCompletionTimeWithReleaseTimes.WellFormed i ∧
      TwoProcessorReleaseTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorReleaseTotalCompletion
