/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ONE- AND TWO-PROCESSOR TASKS ON TWO PROCESSORS, maximum lateness (`P2|size_i|Lmax`)
is NP-complete

Source:
C.-Y. Lee and X. Cai, "Scheduling one and two-processor tasks on two parallel processors",
IIE Transactions 31 (1999), 445-455, doi:10.1080/07408179908969847 (Appendix);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multiprocessor tasks on parallel processors" (`P2|size_i|L_max`, minimal NP-hard in the
strong sense, citing Lee and Cai 1999).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeMaxLateness

/-!
# ONE- AND TWO-PROCESSOR TASKS ON TWO PROCESSORS, maximum lateness, is NP-complete

INSTANCE: `m = 2` identical parallel processors, each processing at most one task at a time;
tasks `1, …, n` (`n ≥ 1`), task `i` with a processing time `p_i ∈ ℤ₀⁺`, a size
`size_i ∈ {1, 2}` (the task requires `size_i` processors simultaneously during its whole
uninterrupted processing, and any `size_i` processors may be used) and a due date `d_i ∈ ℤ₀⁺`;
and an integer bound `K`. QUESTION: is there a feasible schedule whose maximum lateness
`max_i (C_i - d_i)` is at most `K`, where `C_i` is the completion time of task `i`?

This is `P2|size_i|L_max` in the Brucker-Knust classification; Lee and Cai prove in their
Appendix that minimizing the maximum lateness of one- and two-processor tasks on two parallel
processors is NP-complete in the strong sense. Tasks are listed one per entry as
`(p_i, size_i, d_i)`; tasks are `Fin n`. A schedule gives each task `j` a start time `S j` and
the set `π j` of the `size_j` processors it uses during `[S j, S j + p_j)`; two different tasks
that share a processor have disjoint processing intervals. There is at least one task, since
`max_i (C_i - d_i)` is undefined for an empty task set. The bound is an integer, encoded as a
pair `(K⁺, K⁻)` representing `K⁺ - K⁻` as in `ZeroOneILPWanted`, and `C_j - d_j ≤ K⁺ - K⁻` is
stated over `ℕ` as `C_j + K⁻ ≤ d_j + K⁺`. Nonnegative due dates lose no generality: replacing every
`d_i` by `d_i + c` and `K` by `K - c` changes no answer. Start times are natural numbers:
rounding all start times down keeps disjoint processing intervals disjoint, since the processing
times are integers, and increases no completion time. Membership in NP is the certificate
argument: the start time (at most `max_j d_j + K⁺`) and the processor set of every task, checked
pairwise in polynomial time. Binary encoding of all numbers; the source proves NP-hardness in the
strong sense, which this statement does not record.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the tasks, task `j` being the `j`-th triple `(p_j, size_j, d_j)` of its
processing time, its size and its due date, and the bound `K` as a pair `(K⁺, K⁻)` with
`K = K⁺ - K⁻`. -/
abbrev TwoProcessorTaskSizeMaxLatenessInstance := List (ℕ × ℕ × ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: there is at least one task, and every task has size `1` or
`2`. -/
def WellFormed (i : TwoProcessorTaskSizeMaxLatenessInstance) : Prop :=
  i.1 ≠ [] ∧ ∀ x ∈ i.1, x.2.1 = 1 ∨ x.2.1 = 2

/-- Some schedule, with start times `S j` and processor sets `π j ⊆ {0, 1}` of `size_j`
processors, runs two different tasks that share a processor during disjoint intervals
`[S j, S j + p_j)`, and completes every task `j` with lateness `C_j - d_j ≤ K⁺ - K⁻`, that is
`S j + p_j + K⁻ ≤ d_j + K⁺`. -/
def TwoProcessorTaskSizeMaxLatenessFeasible (i : TwoProcessorTaskSizeMaxLatenessInstance) :
    Prop :=
  ∃ S : Fin i.1.length → ℕ, ∃ π : Fin i.1.length → Finset (Fin 2),
    (∀ j, (π j).card = (i.1.get j).2.1) ∧
    (∀ j k, j ≠ k → ¬ Disjoint (π j) (π k) →
      Disjoint (Finset.Ico (S j) (S j + (i.1.get j).1))
        (Finset.Ico (S k) (S k + (i.1.get k).1))) ∧
    ∀ j, S j + (i.1.get j).1 + i.2.2 ≤ (i.1.get j).2.2 + i.2.1

open Classical in
/-- `P2|size_i|Lmax` as a decision problem over bitstrings. -/
noncomputable def twoProcessorTaskSizeMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTaskSizeMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTaskSizeMaxLatenessFeasible i)
  | none => false

/-- **ONE- AND TWO-PROCESSOR TASKS ON TWO PROCESSORS, maximum lateness (`P2|size_i|Lmax`) is
NP-complete.** Source: Lee and Cai (1999), Appendix, as recorded in the Brucker-Knust
classification. -/
public theorem_wanted twoProcessorTaskSizeMaxLateness_npComplete :
    twoProcessorTaskSizeMaxLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorTaskSizeMaxLatenessDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeMaxLateness
