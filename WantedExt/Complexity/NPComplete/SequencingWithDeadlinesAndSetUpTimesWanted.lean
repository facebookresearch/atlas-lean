/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING WITH DEADLINES AND SET-UP TIMES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS6] SEQUENCING WITH DEADLINES
AND SET-UP TIMES;
J. Bruno and P. Downey, "Complexity of task sequencing with deadlines, set-up times and
changeover costs", SIAM Journal on Computing 7 (1978), 393-404, doi:10.1137/0207031.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Function.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingWithDeadlinesAndSetUpTimes

/-!
# SEQUENCING WITH DEADLINES AND SET-UP TIMES is NP-complete

INSTANCE: a set `C` of "compilers", a set `T` of tasks, for each `t ∈ T` a length
`l(t) ∈ ℤ⁺`, a deadline `d(t) ∈ ℤ⁺` and a compiler `k(t) ∈ C`, and for each `c ∈ C` a
"set-up time" `l(c) ∈ ℤ₀⁺`. QUESTION: is there a one-processor schedule `σ` for `T` that meets
all the task deadlines and that satisfies the additional constraint that, whenever two tasks
`t` and `t'` with `σ(t) < σ(t')` are scheduled "consecutively" (no other task `t''` has
`σ(t) < σ(t'') < σ(t')`) and have different compilers (`k(t) ≠ k(t')`), then
`σ(t') ≥ σ(t) + l(t) + l(k(t'))`?

A one-processor schedule (Garey and Johnson, [SS1]) is a one-to-one function `σ : T → ℤ₀⁺`
with `σ(t) > σ(t')` implying `σ(t) ≥ σ(t') + l(t')`; it meets the deadlines when
`σ(t) + l(t) ≤ d(t)` for every task. The compilers are `0, …, |C| - 1`, one per listed set-up
time, and the tasks are `Fin n`, one per listed triple `(l(t), d(t), k(t))`. Binary encoding
of all numbers (Garey and Johnson record that strong NP-completeness is open).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the set-up times `l(c)` of the compilers `c = 0, …, |C| - 1`, and the tasks,
task `t` being the `t`-th triple `(l(t), d(t), k(t))` of length, deadline and compiler. -/
abbrev SequencingWithDeadlinesAndSetUpTimesInstance := List ℕ × List (ℕ × ℕ × ℕ)

/-- The tasks of the instance, `Fin n` for `n` listed triples. -/
abbrev Task (i : SequencingWithDeadlinesAndSetUpTimesInstance) : Type := Fin i.2.length

/-- The length `l(t)` of task `t`. -/
def taskLength (i : SequencingWithDeadlinesAndSetUpTimesInstance) (t : Task i) : ℕ :=
  (i.2.get t).1

/-- The deadline `d(t)` of task `t`. -/
def deadline (i : SequencingWithDeadlinesAndSetUpTimesInstance) (t : Task i) : ℕ :=
  (i.2.get t).2.1

/-- The compiler `k(t)` of task `t`. -/
def compiler (i : SequencingWithDeadlinesAndSetUpTimesInstance) (t : Task i) : ℕ :=
  (i.2.get t).2.2

/-- The set-up time `l(c)` of compiler `c`. -/
def setUpTime (i : SequencingWithDeadlinesAndSetUpTimesInstance) (c : ℕ) : ℕ :=
  i.1.getD c 0

/-- A one-processor schedule for tasks with lengths `l` (Garey and Johnson, [SS1]): a
one-to-one function `σ` into `ℤ₀⁺` with `σ(t) > σ(t')` implying `σ(t) ≥ σ(t') + l(t')`. -/
def IsOneProcessorSchedule {n : ℕ} (l : Fin n → ℕ) (σ : Fin n → ℕ) : Prop :=
  Function.Injective σ ∧ ∀ t t', σ t' < σ t → σ t' + l t' ≤ σ t

/-- Well-formedness of an instance: every task has a positive length, a positive deadline,
and a compiler in `C`. -/
def WellFormed (i : SequencingWithDeadlinesAndSetUpTimesInstance) : Prop :=
  ∀ x ∈ i.2, 0 < x.1 ∧ 0 < x.2.1 ∧ x.2.2 < i.1.length

/-- Some one-processor schedule meets every deadline and, whenever `t'` directly follows `t`
and their compilers differ, leaves the set-up time of `t'`'s compiler between them. -/
def SequencingWithDeadlinesAndSetUpTimesFeasible
    (i : SequencingWithDeadlinesAndSetUpTimesInstance) : Prop :=
  ∃ σ : Task i → ℕ, IsOneProcessorSchedule (taskLength i) σ ∧
    (∀ t, σ t + taskLength i t ≤ deadline i t) ∧
    ∀ t t', σ t < σ t' → (∀ t'', ¬ (σ t < σ t'' ∧ σ t'' < σ t')) →
      compiler i t ≠ compiler i t' →
        σ t + taskLength i t + setUpTime i (compiler i t') ≤ σ t'

open Classical in
/-- SEQUENCING WITH DEADLINES AND SET-UP TIMES as a decision problem over bitstrings. -/
noncomputable def sequencingWithDeadlinesAndSetUpTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SequencingWithDeadlinesAndSetUpTimesInstance) x with
  | some i => decide (WellFormed i ∧ SequencingWithDeadlinesAndSetUpTimesFeasible i)
  | none => false

/-- **SEQUENCING WITH DEADLINES AND SET-UP TIMES is NP-complete.** Source: Garey and Johnson
(1979), [SS6]; Bruno and Downey (1978). -/
public theorem_wanted sequencingWithDeadlinesAndSetUpTimes_npComplete :
    sequencingWithDeadlinesAndSetUpTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sequencingWithDeadlinesAndSetUpTimesDec

end MetaMathlibExt.Complexity.NPComplete.SequencingWithDeadlinesAndSetUpTimes
