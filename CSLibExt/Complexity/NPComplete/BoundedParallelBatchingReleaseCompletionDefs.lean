/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED PARALLEL-BATCHING TOTAL COMPLETION TIME WITH RELEASE DATES (1|p-batch;r_i;b<n|ΣC_i): definitions
is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch;r_i;b<n|ΣC_i`: minimal NP-hard in the strong sense, by reduction from
the single machine problem `1|r_i|ΣC_i`; J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker,
"Complexity of machine scheduling problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X (`1|r_j|ΣC_j` strongly NP-hard); parallel-batching model from
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseCompletion

/-- An instance: the batch capacity `b`, the jobs as pairs `(p_j, r_j)` of processing time and
release date, and the bound `K`. -/
abbrev BoundedParallelBatchingReleaseCompletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The number `n` of jobs. -/
abbrev numJobs (i : BoundedParallelBatchingReleaseCompletionInstance) : ℕ := i.2.1.length

/-- The processing time `p_j` of job `j`. -/
def proc (i : BoundedParallelBatchingReleaseCompletionInstance) (j : Fin (numJobs i)) : ℕ :=
  (i.2.1.get j).1

/-- The release date `r_j` of job `j`. -/
def release (i : BoundedParallelBatchingReleaseCompletionInstance) (j : Fin (numJobs i)) : ℕ :=
  (i.2.1.get j).2

/-- The processing time of batch `k` when job `j` with processing time `p j` is in batch `B j`:
the largest processing time of the jobs of the batch (`0` for an empty batch). -/
def batchLength {n : ℕ} (p : Fin n → ℕ) (B : Fin n → ℕ) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun j => B j = k)).sup p

/-- The batches are processed one after another in the order of their indices: when
`B j < B j'`, batch `B j'` starts (at `S (B j')`) only after batch `B j` has completed. -/
def IsBatchSequence {n : ℕ} (p : Fin n → ℕ) (B : Fin n → ℕ) (S : ℕ → ℕ) : Prop :=
  ∀ j j', B j < B j' → S (B j) + batchLength p B (B j) ≤ S (B j')

/-- The completion time of job `j`: the completion time `S (B j) + P (B j)` of its batch. -/
def completion {n : ℕ} (p : Fin n → ℕ) (B : Fin n → ℕ) (S : ℕ → ℕ) (j : Fin n) : ℕ :=
  S (B j) + batchLength p B (B j)

/-- Well-formedness of an instance: the batch capacity `b` is positive and less than the number
`n` of jobs, every processing time is positive, and the bound `K` is positive. -/
def WellFormed (i : BoundedParallelBatchingReleaseCompletionInstance) : Prop :=
  0 < i.1 ∧ i.1 < numJobs i ∧ (∀ job ∈ i.2.1, 0 < job.1) ∧ 0 < i.2.2

/-- Some parallel-batching schedule has at most `b` jobs in every batch, starts every job (at the
start `S (B j)` of its batch) no earlier than its release date, and has total completion time at
most `K`. -/
def BoundedParallelBatchingReleaseCompletionFeasible
    (i : BoundedParallelBatchingReleaseCompletionInstance) : Prop :=
  ∃ (B : Fin (numJobs i) → ℕ) (S : ℕ → ℕ), IsBatchSequence (proc i) B S ∧
    (∀ k, (Finset.univ.filter (fun j => B j = k)).card ≤ i.1) ∧
    (∀ j, release i j ≤ S (B j)) ∧ ∑ j, completion (proc i) B S j ≤ i.2.2

open Classical in
/-- BOUNDED PARALLEL-BATCHING TOTAL COMPLETION TIME WITH RELEASE DATES as a decision problem over
bitstrings. -/
noncomputable def boundedParallelBatchingReleaseCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedParallelBatchingReleaseCompletionInstance) x with
  | some i => decide (WellFormed i ∧ BoundedParallelBatchingReleaseCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseCompletion
