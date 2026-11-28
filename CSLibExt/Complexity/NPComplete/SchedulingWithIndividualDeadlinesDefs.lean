/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING WITH INDIVIDUAL DEADLINES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS11] SCHEDULING WITH INDIVIDUAL
DEADLINES;
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlines

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

end MetaMathlibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlines
