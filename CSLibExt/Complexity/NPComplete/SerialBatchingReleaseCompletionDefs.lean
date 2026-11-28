/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIAL-BATCHING TOTAL COMPLETION TIME WITH RELEASE DATES (1|s-batch;r_i|ΣC_i): definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `s-batch` (serial
batching), entry `1|s-batch;r_i|ΣC_i`: minimal NP-hard in the strong sense, citing Lenstra,
Rinnooy Kan and Brucker (1977); J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity
of machine scheduling problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X (`1|r_j|ΣC_j` strongly NP-hard); serial-batching model from
P. Baptiste and A. Jouglet, RAIRO Operations Research 35(1) (2001), 107-115,
doi:10.1051/ro:2001105.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SerialBatchingReleaseCompletion

/-- An instance: the setup time `s`, the jobs as pairs `(p_j, r_j)` of
processing time and release date, and the bound `K`. -/
abbrev SerialBatchingReleaseCompletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The number of jobs. -/
abbrev numJobs (i : SerialBatchingReleaseCompletionInstance) : ℕ := i.2.1.length

/-- The processing time of job `j`. -/
def proc (i : SerialBatchingReleaseCompletionInstance) (j : Fin (numJobs i)) : ℕ :=
  (i.2.1.get j).1

/-- The completion time of batch `k` when job `j` is in batch `b j` and batch `k` starts its setup
at `S k`: setup, then the jobs of the batch one after another. -/
def batchCompletion (i : SerialBatchingReleaseCompletionInstance)
    (b : Fin (numJobs i) → ℕ) (S : ℕ → ℕ) (k : ℕ) : ℕ :=
  S k + i.1 + ∑ j ∈ Finset.univ.filter (fun j => b j = k), proc i j

/-- The batches are processed one after another in the order of their indices: a batch starts
its setup only after every nonempty batch with a smaller index has completed. -/
def IsBatchSchedule (i : SerialBatchingReleaseCompletionInstance)
    (b : Fin (numJobs i) → ℕ) (S : ℕ → ℕ) : Prop :=
  ∀ j j', b j < b j' → batchCompletion i b S (b j) ≤ S (b j')

/-- The completion time of job `j`: the completion time of its batch. -/
def completion (i : SerialBatchingReleaseCompletionInstance)
    (b : Fin (numJobs i) → ℕ) (S : ℕ → ℕ) (j : Fin (numJobs i)) : ℕ :=
  batchCompletion i b S (b j)

/-- The release date of job `j`. -/
def release (i : SerialBatchingReleaseCompletionInstance) (j : Fin (numJobs i)) : ℕ :=
  (i.2.1.get j).2

/-- Well-formedness of an instance: the setup time `s`, every processing time and the bound `K` are
positive. -/
def WellFormed (i : SerialBatchingReleaseCompletionInstance) : Prop :=
  0 < i.1 ∧ (∀ job ∈ i.2.1, 0 < job.1) ∧ 0 < i.2.2

/-- Some serial-batching schedule starts every job (at the start `S (b j) + s` of its batch's
processing) no earlier than its release date and has total completion time at most `K`. -/
def SerialBatchingReleaseCompletionFeasible
    (i : SerialBatchingReleaseCompletionInstance) : Prop :=
  ∃ (b : Fin (numJobs i) → ℕ) (S : ℕ → ℕ), IsBatchSchedule i b S ∧
    (∀ j, release i j ≤ S (b j) + i.1) ∧ ∑ j, completion i b S j ≤ i.2.2

open Classical in
/-- SERIAL-BATCHING TOTAL COMPLETION TIME WITH RELEASE DATES as a decision problem over
bitstrings. -/
noncomputable def serialBatchingReleaseCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SerialBatchingReleaseCompletionInstance) x with
  | some i => decide (WellFormed i ∧ SerialBatchingReleaseCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SerialBatchingReleaseCompletion
