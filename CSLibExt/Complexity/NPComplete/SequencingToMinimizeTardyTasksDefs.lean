/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE TARDY TASKS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS2] SEQUENCING TO MINIMIZE
TARDY TASKS, and Section 3.2.3, Theorem 3.10, p. 73 (MINIMUM TARDINESS SEQUENCING,
transformation from CLIQUE);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Defs.Unbundled
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeTardyTasks

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: the pairs `(l(t), d(t))` of length and deadline of the tasks `0, …, n - 1`,
the pairs `(t, t')` with `t < t'`, and the bound `K`. -/
abbrev SequencingToMinimizeTardyTasksInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin n` for `n` listed tasks. -/
abbrev Task (i : SequencingToMinimizeTardyTasksInstance) : Type := Fin i.1.length

/-- The length `l(t)` of task `t`. -/
def length (i : SequencingToMinimizeTardyTasksInstance) (t : Task i) : ℕ :=
  (i.1.get t).1

/-- The deadline `d(t)` of task `t`. -/
def deadline (i : SequencingToMinimizeTardyTasksInstance) (t : Task i) : ℕ :=
  (i.1.get t).2

/-- The precedence relation: `t < t'` when the pair `(t, t')` is listed. -/
def Prec (i : SequencingToMinimizeTardyTasksInstance) (t t' : Task i) : Prop :=
  ((t : ℕ), (t' : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: every length and deadline is positive, `0 < K ≤ |T|`, every
listed pair names two tasks, and the listed pairs form a strict partial order. -/
def WellFormed (i : SequencingToMinimizeTardyTasksInstance) : Prop :=
  (∀ x ∈ i.1, 0 < x.1 ∧ 0 < x.2) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1.length ∧
    (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧ IsStrictOrder (Task i) (Prec i)

/-- Some one-processor schedule obeys the precedence constraints and has at most `K` tardy
tasks, those with `σ(t) + l(t) > d(t)`. -/
def SequencingToMinimizeTardyTasksFeasible (i : SequencingToMinimizeTardyTasksInstance) :
    Prop :=
  ∃ σ : Task i → ℕ, IsOneProcessorSchedule (length i) σ ∧
    (∀ t t', Prec i t t' → σ t + length i t ≤ σ t') ∧
    (Finset.univ.filter fun t => deadline i t < σ t + length i t).card ≤ i.2.2

open Classical in
/-- SEQUENCING TO MINIMIZE TARDY TASKS as a decision problem over bitstrings. -/
noncomputable def sequencingToMinimizeTardyTasksDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SequencingToMinimizeTardyTasksInstance) x with
  | some i => decide (WellFormed i ∧ SequencingToMinimizeTardyTasksFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeTardyTasks
