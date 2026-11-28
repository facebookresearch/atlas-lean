/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL PROCESSOR TOTAL FLOW TIME: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM PARALLEL PROCESSOR TOTAL FLOW TIME (decision version);
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X (the case `m = 1`, `1|rⱼ|∑ Cⱼ`, is strongly NP-hard).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TotalCompletionTimeWithReleaseTimesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelProcessorTotalFlowTime

open TotalCompletionTimeWithReleaseTimes (TotalCompletionTimeWithReleaseTimesInstance Task
  taskLength releaseTime)

/-- An instance: the tasks as pairs `(l(t), r(t))`, the number `m` of processors, and `K`. -/
abbrev ParallelProcessorTotalFlowTimeInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- The tasks with their lengths and release times, as an instance of the one-processor problem
(the bound component is `K`). -/
abbrev tasks (i : ParallelProcessorTotalFlowTimeInstance) :
    TotalCompletionTimeWithReleaseTimesInstance :=
  (i.1, i.2.2)

/-- Well-formedness of an instance: every length and every release time is positive, `m` is
positive, and `K` is positive. -/
def WellFormed (i : ParallelProcessorTotalFlowTimeInstance) : Prop :=
  (∀ x ∈ i.1, 0 < x.1 ∧ 0 < x.2) ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- Some `m`-processor schedule (start times `σ`, processors `p`) runs at most one task at a
time on each processor, starts every task no earlier than its release time, and has total flow
time `∑ₜ (σ(t) + l(t) - r(t))` at most `K`. -/
def ParallelProcessorTotalFlowTimeFeasible (i : ParallelProcessorTotalFlowTimeInstance) :
    Prop :=
  ∃ (σ : Task (tasks i) → ℕ) (p : Task (tasks i) → Fin i.2.1),
    (∀ t t', t ≠ t' → p t = p t' →
      σ t + taskLength (tasks i) t ≤ σ t' ∨ σ t' + taskLength (tasks i) t' ≤ σ t) ∧
    (∀ t, releaseTime (tasks i) t ≤ σ t) ∧
    ∑ t, (σ t + taskLength (tasks i) t - releaseTime (tasks i) t) ≤ i.2.2

open Classical in
/-- PARALLEL PROCESSOR TOTAL FLOW TIME as a decision problem over bitstrings. -/
noncomputable def parallelProcessorTotalFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ParallelProcessorTotalFlowTimeInstance) x with
  | some i => decide (WellFormed i ∧ ParallelProcessorTotalFlowTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ParallelProcessorTotalFlowTime
