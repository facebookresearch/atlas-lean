/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIAL-BATCHING TOTAL COMPLETION TIME WITH RELEASE DATES (1|s-batch;r_i|ΣC_i) is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SerialBatchingReleaseCompletion

/-!
# SERIAL-BATCHING TOTAL COMPLETION TIME WITH RELEASE DATES (1|s-batch;r_i|ΣC_i) is NP-complete

INSTANCE: jobs `1, …, n` with positive processing times `p_j` and release dates `r_j` (natural
numbers), a positive setup time `s`, and a positive bound `K`.
QUESTION: is there a serial-batching schedule on one machine in which no job starts before its
release date and whose total completion time `∑_j C_j` is at most `K`?

Processing times and the bound are positive, as in the classical problem `1|r_j|ΣC_j` whose
NP-hardness the Brucker-Knust entry cites (the repository's
`TotalCompletionTimeWithReleaseTimesWanted` states it with the same conditions); this is the
positive-processing-time variant, and zero-length jobs are not instances.

Serial batching (Baptiste and Jouglet 2001; Brucker and Knust's class `s-batch`): the jobs are
partitioned into batches processed one after another on the machine; a constant setup time `s`
precedes every batch; the length of a batch is the sum of the processing times of its jobs; all
jobs of a batch start together, when the batch's processing starts, and complete together, when
it completes. A schedule puts job `j` into batch `b j` and starts the setup of batch `k` at time
`S k`: batch `k` is set up during `[S k, S k + s)` and processes its jobs during
`[S k + s, S k + s + p(batch k))`, and a batch with a larger index starts only after every
nonempty batch with a smaller index has completed. Empty batch indices play no role. The setup
time is a positive natural number.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`; numbers are in binary encoding.
Undecodable bitstrings, and bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SERIAL-BATCHING TOTAL COMPLETION TIME WITH RELEASE DATES is NP-complete.**
Source: Brucker and Knust, class s-batch; Lenstra, Rinnooy Kan and Brucker (1977). -/
public theorem_wanted serialBatchingReleaseCompletion_npComplete :
    serialBatchingReleaseCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L serialBatchingReleaseCompletionDec

end MetaMathlibExt.Complexity.NPComplete.SerialBatchingReleaseCompletion
