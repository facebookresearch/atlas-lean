/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING WITH INDIVIDUAL DEADLINES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS11] SCHEDULING WITH INDIVIDUAL
DEADLINES;
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlines

/-!
# SCHEDULING WITH INDIVIDUAL DEADLINES is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, a number `m ∈ ℤ⁺` of processors, a
partial order `<` on `T`, and for each task `t ∈ T` a deadline `d(t) ∈ ℤ⁺`. QUESTION: is there an
`m`-processor schedule `σ` for `T` that obeys the precedence constraints and meets all the
deadlines, i.e., `σ(t) + l(t) ≤ d(t)` for all `t ∈ T`?

An `m`-processor schedule is a start time `σ(t) ∈ ℤ₀⁺` for each task such that at every time `u`
at most `m` tasks run (`σ(t) ≤ u < σ(t) + l(t)`); it obeys the precedence constraints when
`t < t'` implies `σ(t') ≥ σ(t) + l(t)`. Tasks are `Fin n`, one per deadline. The partial order is
given by the list of its pairs `(t, t')` with `t < t'`, required to be a strict order (Mathlib's
`IsStrictOrder`: irreflexive and transitive). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of processors `m`, the pairs `(t, t')` with `t < t'`, and the
deadlines `d(0), …, d(n - 1)` (tasks `Fin n`). -/
abbrev SchedulingWithIndividualDeadlinesInstance := ℕ × List (ℕ × ℕ) × List ℕ

/-- The tasks of the instance, `Fin n` for `n` deadlines. -/
abbrev Task (i : SchedulingWithIndividualDeadlinesInstance) : Type := Fin i.2.2.length

/-- The precedence relation: `t < t'` when the pair `(t, t')` is listed. -/
def Prec (i : SchedulingWithIndividualDeadlinesInstance) (t t' : Task i) : Prop :=
  ((t : ℕ), (t' : ℕ)) ∈ i.2.1

/-- The deadline `d(t)` of task `t`. -/
def deadline (i : SchedulingWithIndividualDeadlinesInstance) (t : Task i) : ℕ :=
  i.2.2.getD t 0

/-- The tasks running at time `u` under `σ`: `σ(t) ≤ u < σ(t) + l(t)` with `l(t) = 1`. -/
def running (i : SchedulingWithIndividualDeadlinesInstance) (σ : Task i → ℕ) (u : ℕ) :
    Finset (Task i) :=
  Finset.univ.filter fun t => σ t ≤ u ∧ u < σ t + 1

/-- Well-formedness of an instance: `0 < m`, every listed pair names two tasks, the listed pairs
form a strict partial order, and every deadline is positive. -/
def WellFormed (i : SchedulingWithIndividualDeadlinesInstance) : Prop :=
  0 < i.1 ∧ (∀ p ∈ i.2.1, p.1 < i.2.2.length ∧ p.2 < i.2.2.length) ∧
    IsStrictOrder (Task i) (Prec i) ∧ ∀ d ∈ i.2.2, 0 < d

/-- Some `m`-processor schedule of the unit-length tasks obeys the precedence constraints and
meets every task's deadline. -/
def SchedulingWithIndividualDeadlinesFeasible (i : SchedulingWithIndividualDeadlinesInstance) :
    Prop :=
  ∃ σ : Task i → ℕ, (∀ u, (running i σ u).card ≤ i.1) ∧
    (∀ t t', Prec i t t' → σ t + 1 ≤ σ t') ∧ ∀ t, σ t + 1 ≤ deadline i t

open Classical in
/-- SCHEDULING WITH INDIVIDUAL DEADLINES as a decision problem over bitstrings. -/
noncomputable def schedulingWithIndividualDeadlinesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SchedulingWithIndividualDeadlinesInstance) x with
  | some i => decide (WellFormed i ∧ SchedulingWithIndividualDeadlinesFeasible i)
  | none => false

/-- **SCHEDULING WITH INDIVIDUAL DEADLINES is NP-complete.** Source: Garey and Johnson
(1979), [SS11]; Brucker, Garey and Johnson (1977). -/
public theorem_wanted schedulingWithIndividualDeadlines_npComplete :
    schedulingWithIndividualDeadlinesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L schedulingWithIndividualDeadlinesDec

end MetaMathlibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlines
