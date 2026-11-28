/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIAL-BATCHING TOTAL WEIGHTED COMPLETION TIME (1|s-batch|Σw_iC_i): definitions

Source:
S. Albers and P. Brucker, "The complexity of one-machine batching problems", Discrete Applied
Mathematics 47(2) (1993), 87-107, doi:10.1016/0166-218X(93)90085-3 (unary NP-hardness; text not
available to the author); P. Baptiste and A. Jouglet, "On minimizing total tardiness in a serial
batching problem", RAIRO Operations Research 35(1) (2001), 107-115, doi:10.1051/ro:2001105
(the model, and Table 1: "1|s-batch|Σw_iC_i, unary NP-Hard", citing Albers and Brucker).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SerialBatchingWeightedCompletion

/-- An instance: the setup time `s`, the jobs as pairs `(p_j, w_j)` of
processing time and weight, and the bound `K`. -/
abbrev SerialBatchingWeightedCompletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The number of jobs. -/
abbrev numJobs (i : SerialBatchingWeightedCompletionInstance) : ℕ := i.2.1.length

/-- The processing time of job `j`. -/
def proc (i : SerialBatchingWeightedCompletionInstance) (j : Fin (numJobs i)) : ℕ :=
  (i.2.1.get j).1

/-- The completion time of batch `k` when job `j` is in batch `b j` and batch `k` starts its setup
at `S k`: setup, then the jobs of the batch one after another. -/
def batchCompletion (i : SerialBatchingWeightedCompletionInstance)
    (b : Fin (numJobs i) → ℕ) (S : ℕ → ℕ) (k : ℕ) : ℕ :=
  S k + i.1 + ∑ j ∈ Finset.univ.filter (fun j => b j = k), proc i j

/-- The batches are processed one after another in the order of their indices: a batch starts
its setup only after every nonempty batch with a smaller index has completed. -/
def IsBatchSchedule (i : SerialBatchingWeightedCompletionInstance)
    (b : Fin (numJobs i) → ℕ) (S : ℕ → ℕ) : Prop :=
  ∀ j j', b j < b j' → batchCompletion i b S (b j) ≤ S (b j')

/-- The completion time of job `j`: the completion time of its batch. -/
def completion (i : SerialBatchingWeightedCompletionInstance)
    (b : Fin (numJobs i) → ℕ) (S : ℕ → ℕ) (j : Fin (numJobs i)) : ℕ :=
  batchCompletion i b S (b j)

/-- The weight of job `j`. -/
def weight (i : SerialBatchingWeightedCompletionInstance) (j : Fin (numJobs i)) : ℕ :=
  (i.2.1.get j).2

/-- Well-formedness of an instance: the setup time `s` is positive. -/
def WellFormed (i : SerialBatchingWeightedCompletionInstance) : Prop :=
  0 < i.1

/-- Some serial-batching schedule has total weighted completion time at most `K`. -/
def SerialBatchingWeightedCompletionFeasible
    (i : SerialBatchingWeightedCompletionInstance) : Prop :=
  ∃ (b : Fin (numJobs i) → ℕ) (S : ℕ → ℕ), IsBatchSchedule i b S ∧
    ∑ j, weight i j * completion i b S j ≤ i.2.2

open Classical in
/-- SERIAL-BATCHING TOTAL WEIGHTED COMPLETION TIME as a decision problem over
bitstrings. -/
noncomputable def serialBatchingWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SerialBatchingWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ SerialBatchingWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SerialBatchingWeightedCompletion
