/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PREEMPTIVE SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME WITH RELEASE TIMES is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Pairwise
public import WantedExt.Complexity.NPComplete.WeightedCompletionTimeWithReleaseTimesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PreemptiveWeightedCompletionTimeWithReleaseTimes

open WeightedCompletionTimeWithReleaseTimes

/-!
# PREEMPTIVE SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME WITH RELEASE TIMES is NP-complete

INSTANCE: a set `T` of tasks, for each task `t ∈ T` a length `l(t) ∈ ℤ⁺`, a release time
`r(t) ∈ ℤ₀⁺` and a weight `w(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there a
preemptive one-processor schedule for `T` that processes no task before its release time and
for which the sum, over all `t ∈ T`, of `w(t)` times the completion time of `t` is `K` or less?

This is the "preemptive" version of Garey and Johnson's [SS4] with individual task release
times in place of the partial order (`1|rⱼ, pmtn|∑ wⱼCⱼ`), as in the comment to [SS4]. The
nonpreemptive problem is `WeightedCompletionTimeWithReleaseTimesWanted`, whose instance class
is the same: its instance (task triples `(l(t), r(t), w(t))` and `K`), the task accessors and
`WellFormed` (all lengths, weights and `K` positive) are reused.

Preemptive schedules are those of Garey and Johnson's [SS12]: an ordinary schedule, except that
each task `t` may be subdivided into subtasks `t₁, …, t_k` of positive integer lengths summing
to `l(t)`, with `σ(tᵢ₊₁) ≥ σ(tᵢ) + l(tᵢ)`; the subtasks of all tasks form a one-processor
schedule. With integer start times and lengths, such a schedule is the same as giving each task
`t` a set `S(t)` of exactly `l(t)` unit time slots `[u, u + 1)`, `u ∈ ℤ₀⁺`, no slot used by two
tasks (a subtask starting at `u` with length `m` uses the slots `u, …, u + m - 1`; conversely
the maximal runs of consecutive slots of `S(t)` are its subtasks). The release time constraint
`σ(t₁) ≥ r(t)` says that every slot of `t` is at least `r(t)`, and the completion time of `t`,
`σ(t_k) + l(t_k)`, is one more than its last slot. Labetoulle, Lawler, Lenstra and Rinnooy Kan
allow preemption at arbitrary real times; with integer data this does not change the minimum:
processing, at every moment, the released unfinished task that completes first in a given
preemptive schedule completes no task later, and switches tasks only at release times and
completions, which are then integers.

Membership in NP: the slot sets can be exponentially large, but by the same argument some
schedule of minimum cost is the one that, at every moment, processes the released unfinished
task that comes first in a fixed order of the tasks; that order is a certificate of polynomial
size, and its schedule (at most `2 |T|` pieces, changing tasks only at release times and
completions) and cost are computed in polynomial time.

The tasks are `Fin n`, one per listed triple. Binary encoding of all numbers (the problem is
NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PREEMPTIVE SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME WITH RELEASE TIMES is
NP-complete.** Source: Garey and Johnson (1979), [SS4], comment; Labetoulle, Lawler, Lenstra,
and Rinnooy Kan (1984), Section 4. -/
public theorem_wanted preemptiveWeightedCompletionTimeWithReleaseTimes_npComplete :
    preemptiveWeightedCompletionTimeWithReleaseTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L preemptiveWeightedCompletionTimeWithReleaseTimesDec

end MetaMathlibExt.Complexity.NPComplete.PreemptiveWeightedCompletionTimeWithReleaseTimes
