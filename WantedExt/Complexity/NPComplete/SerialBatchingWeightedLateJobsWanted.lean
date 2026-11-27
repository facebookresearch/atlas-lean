/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIAL-BATCHING WEIGHTED NUMBER OF LATE JOBS (1|s-batch|Σw_iU_i) is NP-complete

Source:
P. Brucker and M. Y. Kovalyov, "Single machine batch scheduling to minimize the weighted number
of late jobs", Mathematical Methods of Operations Research 43 (1996), 1-8,
doi:10.1007/BF01303431;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.SerialBatchingWeightedCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SerialBatchingWeightedLateJobs

open SerialBatchingWeightedCompletion
  (SerialBatchingWeightedCompletionInstance numJobs IsBatchSchedule completion weight)

/-!
# SERIAL-BATCHING WEIGHTED NUMBER OF LATE JOBS (1|s-batch|Σw_iU_i) is NP-complete

INSTANCE: jobs `1, …, n` with processing times `p_j`, due dates `d_j` and weights `w_j` (natural
numbers), a positive setup time `s`, and a bound `K`.
QUESTION: is there a serial-batching schedule on one machine in which the total weight of the
late jobs, the jobs `j` with `C_j > d_j`, is at most `K`, where `C_j` is the completion time of
job `j`?

Serial batching is as in `SerialBatchingWeightedCompletionWanted` (`1|s-batch|∑ w_i C_i`): the
jobs are partitioned into batches processed one after another; the setup time `s` precedes
every batch; the jobs of a batch are processed consecutively and all complete when the batch
completes. The instance is that module's instance (setup time `s`, pairs `(p_j, w_j)`, bound
`K`) together with the list of due dates, one per job; its batch schedules `IsBatchSchedule`,
job completion times `completion`, weights `weight` and well-formedness (`s > 0`) are reused.

Brucker and Kovalyov (1996) study exactly this problem and state that it "is NP-hard even if
all due dates are equal"; Brucker and Knust's classification (class `bat_s`) lists it as
minimal NP-hard in the ordinary sense, citing Brucker and Kovalyov (1996) and Karp (1972), whose
SEQUENCING problem is `1||∑ w_j U_j`. Numbers are in binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SERIAL-BATCHING WEIGHTED NUMBER OF LATE JOBS (`1|s-batch|∑ w_i U_i`) is NP-complete.**
Source: Brucker and Kovalyov (1996); Karp (1972). -/
public theorem_wanted serialBatchingWeightedLateJobs_npComplete :
    serialBatchingWeightedLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L serialBatchingWeightedLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.SerialBatchingWeightedLateJobs
