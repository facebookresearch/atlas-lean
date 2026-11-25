/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE CHOICE SCHEDULING WITHIN INTERVALS is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 189-203,
doi:10.1016/0196-6774(83)90045-7, problem [1] MULTIPLE CHOICE SCHEDULING WITHIN INTERVALS (the
problem, credited to Simons and Sipser, transformation from 3SAT);
B. Simons and M. Sipser, "On scheduling unit-length jobs with multiple release time/deadline
intervals", Operations Research 32 (1984), 80-88, doi:10.1287/opre.32.1.80.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Fintype.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleChoiceSchedulingWithinIntervals

/-!
# MULTIPLE CHOICE SCHEDULING WITHIN INTERVALS is NP-complete

INSTANCE: a number `m` of processors, a set `T` of tasks, a common task length `l`, and, for each
task `t ∈ T`, a collection `C(t) = {[aᵢ(t), bᵢ(t)] : 1 ≤ i ≤ k(t)}` of permissible scheduling
intervals, with integer endpoints and `0 ≤ aᵢ(t) ≤ bᵢ(t) - l`.
QUESTION: is there an `m`-processor nonpreemptive schedule for `T` that places each task in one
of its permissible intervals, i.e., a function `s : T → ℤ` assigning each task a non-negative
starting time such that (a) at every time `u`, at most `m` tasks `t` have `s(t) ≤ u < s(t) + l`,
and (b) for each `t ∈ T` there is an `i` with `aᵢ(t) ≤ s(t) ≤ bᵢ(t) - l`?

The tasks are `Fin |T|`, task `t` being the `t`-th list of intervals `(aᵢ(t), bᵢ(t))`; starting
times and endpoints are natural numbers (the source's are non-negative integers). Condition (a)
is checked at every natural time `u`: starting times are integers, so the set of tasks running at
a real time `u ≥ 0` is the set running at `⌊u⌋`. Johnson prints condition (a) "for all times
`u > 0`"; over real times this is the same as every natural time, because a real `u ∈ (0, 1)`
sees exactly the tasks running at time `0`. Condition (b) reads `aᵢ(t) ≤ s(t)` and
`s(t) + l ≤ bᵢ(t)`. Simons and Sipser prove the problem NP-complete in the strong sense, already for
every fixed `m ≥ 1`; numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of processors, the common task length `l`, and for each task the
list of its permissible intervals `(aᵢ(t), bᵢ(t))`. -/
abbrev MultipleChoiceSchedulingWithinIntervalsInstance := ℕ × ℕ × List (List (ℕ × ℕ))

/-- Well-formedness of an instance: every permissible interval `[a, b]` has `a ≤ b - l`, i.e.
`a + l ≤ b`. -/
def WellFormed (i : MultipleChoiceSchedulingWithinIntervalsInstance) : Prop :=
  ∀ C ∈ i.2.2, ∀ I ∈ C, I.1 + i.2.1 ≤ I.2

/-- Some starting times `s` run at most `m` tasks at every time and place every task inside one
of its permissible intervals. -/
def MultipleChoiceSchedulingWithinIntervalsFeasible
    (i : MultipleChoiceSchedulingWithinIntervalsInstance) : Prop :=
  ∃ s : Fin i.2.2.length → ℕ,
    (∀ u : ℕ, (Finset.univ.filter fun t => s t ≤ u ∧ u < s t + i.2.1).card ≤ i.1) ∧
      ∀ t : Fin i.2.2.length, ∃ I ∈ i.2.2[t], I.1 ≤ s t ∧ s t + i.2.1 ≤ I.2

open Classical in
/-- MULTIPLE CHOICE SCHEDULING WITHIN INTERVALS as a decision problem over bitstrings. -/
noncomputable def multipleChoiceSchedulingWithinIntervalsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleChoiceSchedulingWithinIntervalsInstance) x with
  | some i => decide (WellFormed i ∧ MultipleChoiceSchedulingWithinIntervalsFeasible i)
  | none => false

/-- **MULTIPLE CHOICE SCHEDULING WITHIN INTERVALS is NP-complete.** Source: Johnson (1983),
problem [1]; Simons and Sipser (1984). -/
public theorem_wanted multipleChoiceSchedulingWithinIntervals_npComplete :
    multipleChoiceSchedulingWithinIntervalsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleChoiceSchedulingWithinIntervalsDec

end MetaMathlibExt.Complexity.NPComplete.MultipleChoiceSchedulingWithinIntervals
