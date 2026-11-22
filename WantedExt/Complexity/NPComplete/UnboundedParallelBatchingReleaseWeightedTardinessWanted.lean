/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNBOUNDED PARALLEL-BATCHING WEIGHTED TARDINESS WITH RELEASE DATES (1|p-batch;r_i|Σw_iT_i)
is NP-complete

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (`1|p-batch|Σw_jT_j` NP-hard);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch;r_i|Σw_iT_i`.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.BoundedParallelBatchingReleaseCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingReleaseWeightedTardiness

open BoundedParallelBatchingReleaseCompletion (IsBatchSequence completion)

/-!
# UNBOUNDED PARALLEL-BATCHING WEIGHTED TARDINESS WITH RELEASE DATES (1|p-batch;r_i|Σw_iT_i)
is NP-complete

INSTANCE: jobs `1, …, n`, each with a processing time `p_j ∈ ℤ⁺`, a release date `r_j`, a due
date `d_j` and a weight `w_j` (nonnegative integers), and a bound `K ∈ ℤ₀⁺`.
QUESTION: is there a parallel-batching schedule on one machine, with no bound on the number of
jobs in a batch and no job started before its release date, whose total weighted tardiness
`∑_j w_j max{0, C_j - d_j}` is at most `K`, where `C_j` is the completion time of job `j`?

Parallel batching is as in `BoundedParallelBatchingReleaseCompletionWanted`
(`1|p-batch;r_i;b<n|ΣC_i`): the jobs are partitioned into batches processed one after another;
all jobs of a batch start together and complete together, and the processing time of a batch is
the largest processing time of its jobs. That module's batch sequence `IsBatchSequence` (job `j`
in batch `B j`, batch `k` started at `S k`) and job completion times `completion` are reused.
This is the unbounded model (`b ≥ n`, Brucker et al. 1998): there is no capacity condition.
Processing times are positive, as in `BoundedParallelBatchingReleaseCompletionWanted`.
Natural-number subtraction truncates at `0`, so `C_j - d_j` is the tardiness
`max{0, C_j - d_j}`.

Hardness: Brucker et al. (1998) prove `1|p-batch|Σw_jT_j` NP-hard; each of its instances is an
instance of this problem with every `r_j = 0` and the same answer, so this problem is NP-hard.
Brucker and Knust's classification (class `bat_p`) lists `1|p-batch;r_i|Σw_iT_i` as maximal
pseudopolynomially solvable, citing Baptiste, Brucker, Knust and Timkovsky (2004); numbers are
in binary encoding. Membership in NP: the batch assignment and the start times form a
certificate, and the earliest start times are at most `max_j r_j + ∑_j p_j`. The jobs are
`Fin n`, one per listed quadruple `(p_j, r_j, d_j, w_j)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs as quadruples `(p_j, r_j, d_j, w_j)` of processing time, release date,
due date and weight, and the bound `K`. -/
abbrev UnboundedParallelBatchingReleaseWeightedTardinessInstance :=
  List (ℕ × ℕ × ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed quadruples. -/
abbrev Job (i : UnboundedParallelBatchingReleaseWeightedTardinessInstance) : Type :=
  Fin i.1.length

/-- The processing time `p_j` of job `j`. -/
def proc (i : UnboundedParallelBatchingReleaseWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The release date `r_j` of job `j`. -/
def release (i : UnboundedParallelBatchingReleaseWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.1

/-- The due date `d_j` of job `j`. -/
def dueDate (i : UnboundedParallelBatchingReleaseWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2.1

/-- The weight `w_j` of job `j`. -/
def weight (i : UnboundedParallelBatchingReleaseWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2.2

/-- Well-formedness of an instance: every processing time is positive. -/
def WellFormed (i : UnboundedParallelBatchingReleaseWeightedTardinessInstance) : Prop :=
  ∀ x ∈ i.1, 0 < x.1

/-- Some parallel-batching schedule starts every job (at the start `S (B j)` of its batch) no
earlier than its release date and has total weighted tardiness `∑_j w_j (C_j - d_j)`
(truncated subtraction) at most `K`. -/
def UnboundedParallelBatchingReleaseWeightedTardinessFeasible
    (i : UnboundedParallelBatchingReleaseWeightedTardinessInstance) : Prop :=
  ∃ (B : Job i → ℕ) (S : ℕ → ℕ), IsBatchSequence (proc i) B S ∧
    (∀ j, release i j ≤ S (B j)) ∧
    ∑ j, weight i j * (completion (proc i) B S j - dueDate i j) ≤ i.2

open Classical in
/-- UNBOUNDED PARALLEL-BATCHING WEIGHTED TARDINESS WITH RELEASE DATES as a decision problem over
bitstrings. -/
noncomputable def unboundedParallelBatchingReleaseWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnboundedParallelBatchingReleaseWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ UnboundedParallelBatchingReleaseWeightedTardinessFeasible i)
  | none => false

/-- **UNBOUNDED PARALLEL-BATCHING WEIGHTED TARDINESS WITH RELEASE DATES
(`1|p-batch;r_i|Σw_iT_i`) is NP-complete.** Source: Brucker et al. (1998); Brucker and Knust,
class bat_p. -/
public theorem_wanted unboundedParallelBatchingReleaseWeightedTardiness_npComplete :
    unboundedParallelBatchingReleaseWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unboundedParallelBatchingReleaseWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingReleaseWeightedTardiness
