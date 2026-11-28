/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE TARDY TASKS with unit lengths and chains: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS2] SEQUENCING TO MINIMIZE TARDY
TASKS (comment: remains NP-complete even if all task lengths are 1 and `<` consists only of
"chains", credited to Lenstra 1977);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 1 (`1|chains, pⱼ = 1|∑ Uⱼ`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Defs.Unbundled
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TardyTasksUnitChains

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: the deadlines `d(0), …, d(n - 1)` of the unit-length tasks, the pairs
`(t, t')` with `t < t'`, and the bound `K`. -/
abbrev TardyTasksUnitChainsInstance := List ℕ × List (ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin n` for `n` deadlines. -/
abbrev Task (i : TardyTasksUnitChainsInstance) : Type := Fin i.1.length

/-- The deadline `d(t)` of task `t`. -/
def deadline (i : TardyTasksUnitChainsInstance) (t : Task i) : ℕ :=
  i.1.get t

/-- The precedence relation: `t < t'` when the pair `(t, t')` is listed. -/
def Prec (i : TardyTasksUnitChainsInstance) (t t' : Task i) : Prop :=
  ((t : ℕ), (t' : ℕ)) ∈ i.2.1

/-- `t` is an immediate predecessor of `t'` (and `t'` an immediate successor of `t`):
`t < t'`, and no task `c` has `t < c < t'`. -/
def ImmediatePredecessor (i : TardyTasksUnitChainsInstance) (t t' : Task i) : Prop :=
  Prec i t t' ∧ ∀ c, ¬ (Prec i t c ∧ Prec i c t')

/-- Well-formedness of an instance: every deadline is positive, `0 < K ≤ |T|`, every listed
pair names two tasks, the listed pairs form a strict partial order, and the order consists of
chains (every task has at most one immediate predecessor and at most one immediate
successor). -/
def WellFormed (i : TardyTasksUnitChainsInstance) : Prop :=
  (∀ d ∈ i.1, 0 < d) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1.length ∧
    (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧
    IsStrictOrder (Task i) (Prec i) ∧
    (∀ t a b, ImmediatePredecessor i a t → ImmediatePredecessor i b t → a = b) ∧
    ∀ t a b, ImmediatePredecessor i t a → ImmediatePredecessor i t b → a = b

/-- Some one-processor schedule of the unit-length tasks obeys the precedence constraints and
has at most `K` tardy tasks, those with `σ(t) + 1 > d(t)`. -/
def TardyTasksUnitChainsFeasible (i : TardyTasksUnitChainsInstance) : Prop :=
  ∃ σ : Task i → ℕ, IsOneProcessorSchedule (fun _ => 1) σ ∧
    (∀ t t', Prec i t t' → σ t + 1 ≤ σ t') ∧
    (Finset.univ.filter fun t => deadline i t < σ t + 1).card ≤ i.2.2

open Classical in
/-- SEQUENCING TO MINIMIZE TARDY TASKS with unit lengths and chains as a decision problem over
bitstrings. -/
noncomputable def tardyTasksUnitChainsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TardyTasksUnitChainsInstance) x with
  | some i => decide (WellFormed i ∧ TardyTasksUnitChainsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TardyTasksUnitChains
