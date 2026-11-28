/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PREEMPTIVE SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME WITH RELEASE TIMES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS4] SEQUENCING TO MINIMIZE
WEIGHTED COMPLETION TIME, p. 237, comment ("If there are individual task release times instead
of deadline, ... The "preemptive" version of this latter problem is NP-complete in the strong
sense [Labetoulle, Lawler, Lenstra, and Rinnooy Kan, 1978]"), and [SS12] PREEMPTIVE SCHEDULING,
p. 240 (preemptive schedules);
J. Labetoulle, E. L. Lawler, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Preemptive scheduling of
uniform machines subject to release dates", in *Progress in Combinatorial Optimization*
(W. R. Pulleyblank, ed.), Academic Press (1984), 245-261,
doi:10.1016/B978-0-12-566780-7.50020-9, Section 4 (`1|rⱼ, pmtn|∑ wⱼCⱼ` is NP-hard, by a
reduction from PARTITION, and NP-hard in the strong sense, by a reduction from 3-PARTITION).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Pairwise
public import CSLibExt.Complexity.NPComplete.WeightedCompletionTimeWithReleaseTimesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PreemptiveWeightedCompletionTimeWithReleaseTimes

open WeightedCompletionTimeWithReleaseTimes

/-- A preemptive one-processor schedule for tasks with lengths `l` (Garey and Johnson, [SS12],
with integer start times): task `t` is processed in the unit time slots `[u, u + 1)` for
`u ∈ S t`, exactly `l(t)` of them, and no slot is used by two different tasks. -/
def IsPreemptiveOneProcessorSchedule {n : ℕ} (l : Fin n → ℕ) (S : Fin n → Finset ℕ) : Prop :=
  (∀ t, (S t).card = l t) ∧ Pairwise fun t t' => Disjoint (S t) (S t')

/-- The completion time of task `t` in the slot schedule `S`: the end `u + 1` of its last slot
`u`. -/
def completionTime {n : ℕ} (S : Fin n → Finset ℕ) (t : Fin n) : ℕ :=
  (S t).sup id + 1

/-- Some preemptive one-processor schedule processes no task before its release time and has
weighted completion time `∑ₜ w(t) · C(t)` at most `K`. -/
def PreemptiveWeightedCompletionTimeWithReleaseTimesFeasible
    (i : WeightedCompletionTimeWithReleaseTimesInstance) : Prop :=
  ∃ S : Task i → Finset ℕ, IsPreemptiveOneProcessorSchedule (taskLength i) S ∧
    (∀ t, ∀ u ∈ S t, releaseTime i t ≤ u) ∧
    ∑ t, weight i t * completionTime S t ≤ i.2

open Classical in
/-- PREEMPTIVE SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME WITH RELEASE TIMES as a
decision problem over bitstrings. -/
noncomputable def preemptiveWeightedCompletionTimeWithReleaseTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedCompletionTimeWithReleaseTimesInstance) x with
  | some i => decide (WellFormed i ∧ PreemptiveWeightedCompletionTimeWithReleaseTimesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PreemptiveWeightedCompletionTimeWithReleaseTimes
