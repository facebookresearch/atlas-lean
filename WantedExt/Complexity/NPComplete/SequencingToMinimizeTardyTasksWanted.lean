/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE TARDY TASKS is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Defs.Unbundled
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeTardyTasks

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# SEQUENCING TO MINIMIZE TARDY TASKS is NP-complete

INSTANCE: a set `T` of tasks, a partial order `<` on `T`, for each task `t ∈ T` a length
`l(t) ∈ ℤ⁺` and a deadline `d(t) ∈ ℤ⁺`, and a positive integer `K ≤ |T|`.
QUESTION: is there a one-processor schedule `σ` for `T` that obeys the precedence constraints,
i.e. such that `t < t'` implies `σ(t) + l(t) ≤ σ(t')`, and such that there are at most `K` tasks
`t ∈ T` for which `σ(t) + l(t) > d(t)`?

Garey and Johnson prove this NP-complete (Section 3.2.3, Theorem 3.10) already for unit lengths
(MINIMUM TARDINESS SEQUENCING, a transformation from CLIQUE), and Lenstra and Rinnooy Kan (Theorem
1) for unit lengths with precedence constraints that consist of chains
(`TardyTasksUnitChainsWanted`, the restriction of this problem stated with the same definitions).
Membership in NP: the schedule is a certificate; its start times can be taken below the total
length, so they have polynomially many bits. Binary encoding of all numbers.

The tasks are `Fin n`, one per listed pair `(l(t), d(t))`. A one-processor schedule is Garey and
Johnson's [SS1] notion, reused from `SequencingToMinimizeWeightedTardinessWanted`
(`IsOneProcessorSchedule`, a one-to-one `σ : T → ℤ₀⁺` with `σ(t) > σ(t')` implying
`σ(t) ≥ σ(t') + l(t')`). The partial order is given by the list of its pairs `(t, t')` with
`t < t'`, required to be a strict order (Mathlib's `IsStrictOrder`), as in
`TardyTasksUnitChainsWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SEQUENCING TO MINIMIZE TARDY TASKS is NP-complete.** Source: Garey and Johnson
(1979), [SS2] and Section 3.2.3; Lenstra and Rinnooy Kan (1980), Theorem 1. -/
public theorem_wanted sequencingToMinimizeTardyTasks_npComplete :
    sequencingToMinimizeTardyTasksDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sequencingToMinimizeTardyTasksDec

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeTardyTasks
