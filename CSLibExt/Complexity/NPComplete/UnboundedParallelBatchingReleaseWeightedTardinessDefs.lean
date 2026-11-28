/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNBOUNDED PARALLEL-BATCHING WEIGHTED TARDINESS WITH RELEASE DATES (1|p-batch;r_i|Σw_iT_i): definitions
is NP-complete

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (`1|p-batch|Σw_jT_j` NP-hard);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `bat_p` (parallel
batching), entry `1|p-batch;r_i|Σw_iT_i`.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.BoundedParallelBatchingReleaseCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingReleaseWeightedTardiness

open BoundedParallelBatchingReleaseCompletion (IsBatchSequence completion)

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

end MetaMathlibExt.Complexity.NPComplete.UnboundedParallelBatchingReleaseWeightedTardiness
