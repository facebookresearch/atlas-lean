/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIAL-BATCHING WEIGHTED NUMBER OF LATE JOBS (1|s-batch|Σw_iU_i): definitions

Source:
P. Brucker and M. Y. Kovalyov, "Single machine batch scheduling to minimize the weighted number
of late jobs", Mathematical Methods of Operations Research 43 (1996), 1-8,
doi:10.1007/BF01303431;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.SerialBatchingWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SerialBatchingWeightedLateJobs

open SerialBatchingWeightedCompletion
  (SerialBatchingWeightedCompletionInstance numJobs IsBatchSchedule completion weight)

/-- An instance: the instance of `SerialBatchingWeightedCompletionWanted` (setup time `s`, pairs
`(p_j, w_j)`, bound `K`) and the due dates `d_j`, one per job. -/
abbrev SerialBatchingWeightedLateJobsInstance := SerialBatchingWeightedCompletionInstance × List ℕ

/-- The due date `d_j` of job `j`. -/
def dueDate (i : SerialBatchingWeightedLateJobsInstance) (j : Fin (numJobs i.1)) : ℕ :=
  i.2.getD j 0

/-- Well-formedness of an instance: the setup time is positive, and there is one due date per
job. -/
def WellFormed (i : SerialBatchingWeightedLateJobsInstance) : Prop :=
  SerialBatchingWeightedCompletion.WellFormed i.1 ∧ i.2.length = numJobs i.1

/-- Some serial-batching schedule has total weight of late jobs (`d_j < C_j`) at most `K`. -/
def SerialBatchingWeightedLateJobsFeasible (i : SerialBatchingWeightedLateJobsInstance) : Prop :=
  ∃ (b : Fin (numJobs i.1) → ℕ) (S : ℕ → ℕ), IsBatchSchedule i.1 b S ∧
    ∑ j ∈ Finset.univ.filter (fun j => dueDate i j < completion i.1 b S j), weight i.1 j ≤
      i.1.2.2

open Classical in
/-- SERIAL-BATCHING WEIGHTED NUMBER OF LATE JOBS as a decision problem over bitstrings. -/
noncomputable def serialBatchingWeightedLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SerialBatchingWeightedLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ SerialBatchingWeightedLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SerialBatchingWeightedLateJobs
