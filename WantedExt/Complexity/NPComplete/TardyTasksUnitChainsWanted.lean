/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE TARDY TASKS with unit lengths and chains is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Defs.Unbundled
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TardyTasksUnitChains

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# SEQUENCING TO MINIMIZE TARDY TASKS with unit lengths and chains is NP-complete

INSTANCE: a set `T` of tasks, a partial order `<` on `T`, for each task `t ∈ T` a length
`l(t) = 1` and a deadline `d(t) ∈ ℤ⁺`, and a positive integer `K ≤ |T|`, where `<` consists only
of "chains" (each task has at most one immediate predecessor and at most one immediate
successor). QUESTION: is there a one-processor schedule `σ` for `T` that obeys the precedence
constraints (`t < t'` implies `σ(t) + l(t) ≤ σ(t')`) and such that there are at most `K` tasks
`t ∈ T` for which `σ(t) + l(t) > d(t)`?

This is SEQUENCING TO MINIMIZE TARDY TASKS ([SS2]) restricted to unit lengths and chain-like
precedence, the case Lenstra and Rinnooy Kan prove NP-hard (`1|chains, pⱼ = 1|∑ Uⱼ`). Since
every length is `1`, the instance lists only the deadlines; the tasks are `Fin n`, one per
listed deadline. A one-processor schedule is Garey and Johnson's [SS1] notion, reused from
`SequencingToMinimizeWeightedTardinessWanted` (`IsOneProcessorSchedule`, a one-to-one
`σ : T → ℤ₀⁺` with `σ(t) > σ(t')` implying `σ(t) ≥ σ(t') + l(t')`). The partial order is
given by the list of its pairs `(t, t')` with `t < t'`, required to be a strict order
(Mathlib's `IsStrictOrder`). The chain condition is the source's parenthetical definition:
`t` is an immediate predecessor of `t'` when `t < t'` and no task `c` has `t < c < t'`.
Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SEQUENCING TO MINIMIZE TARDY TASKS is NP-complete for unit lengths and chains.** Source:
Garey and Johnson (1979), [SS2], comment; Lenstra and Rinnooy Kan (1980), Theorem 1. -/
public theorem_wanted tardyTasksUnitChains_npComplete :
    tardyTasksUnitChainsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tardyTasksUnitChainsDec

end MetaMathlibExt.Complexity.NPComplete.TardyTasksUnitChains
