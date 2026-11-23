/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR TREE-PRECEDENCE SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE
WEIGHTED COMPLETION TIME, comment: if precedence constraints are allowed, the problem is
NP-complete in the strong sense even if all weights are equal, `m = 2`, and the partial order is
either an "in-tree" or an "out-tree";
R. Sethi, "On the complexity of mean flow time scheduling", Mathematics of Operations Research 2
(1977), 320-330, doi:10.1287/moor.2.4.320.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTimeWanted
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorTreePrecedenceCompletionTime

/-!
# TWO-PROCESSOR TREE-PRECEDENCE SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME is NP-complete

This is the variant of SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME ([SS13]) with precedence
constraints, equal weights, `m = 2`, and an in-tree or out-tree partial order.

INSTANCE: a set `T` of tasks, `m = 2` processors, for each task `t ∈ T` a length `l(t) ∈ ℤ⁺` and a
weight `w(t) ∈ ℤ⁺`, all weights equal, a partial order `<` on `T` that is an "in-tree" (no task
has more than one immediate successor) or an "out-tree" (no task has more than one immediate
predecessor), and a positive integer `K`. QUESTION: is there a 2-processor schedule `σ` for `T`
that obeys the precedence constraints (`t < t'` implies `σ(t) + l(t) ≤ σ(t')`) and such that the
sum, over all `t ∈ T`, of `(σ(t) + l(t)) · w(t)` is no more than `K`?

This adds precedence constraints to SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME
(`WantedExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTimeWanted`): an instance
is that problem's instance (`toParent`) plus the list of pairs `(t, t')` with `t < t'`. Its
well-formedness condition, the tasks running at each time (`running`), task lengths and the
weighted completion time are reused unchanged. The precedence constraint is the source's
`t < t'` implies `σ(t) + l(t) ≤ σ(t')` (as in [SS2]). The listed pairs must form a strict partial
order (Mathlib's `IsStrictOrder`), and `t` is an immediate predecessor of `t'` (and `t'` an
immediate successor of `t`) when `t < t'` and no task `c` has `t < c < t'`; the in-tree and
out-tree conditions are the source's parenthetical definitions ([SS11]). Binary encoding of all
numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open SchedulingToMinimizeWeightedCompletionTime
  (SchedulingToMinimizeWeightedCompletionTimeInstance running taskLength weightedCompletionTime)

/-- An instance: the number of processors `m`, one pair `(l(t), w(t))` per task `t`, the bound
`K`, and the pairs `(t, t')` with `t < t'`. -/
abbrev TwoProcessorTreePrecedenceCompletionTimeInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME instance without the precedence
constraints. -/
abbrev toParent (i : TwoProcessorTreePrecedenceCompletionTimeInstance) :
    SchedulingToMinimizeWeightedCompletionTimeInstance :=
  (i.1, i.2.1, i.2.2.1)

/-- The tasks of the instance, `Fin n` for `n` listed pairs `(l(t), w(t))`. -/
abbrev Task (i : TwoProcessorTreePrecedenceCompletionTimeInstance) : Type := Fin i.2.1.length

/-- The precedence relation: `t < t'` when the pair `(t, t')` is listed. -/
def Prec (i : TwoProcessorTreePrecedenceCompletionTimeInstance) (t t' : Task i) : Prop :=
  ((t : ℕ), (t' : ℕ)) ∈ i.2.2.2

/-- `t` is an immediate predecessor of `t'` (and `t'` an immediate successor of `t`): `t < t'`,
and no task `c` has `t < c < t'`. -/
def ImmediatePredecessor (i : TwoProcessorTreePrecedenceCompletionTimeInstance)
    (t t' : Task i) : Prop :=
  Prec i t t' ∧ ∀ c, ¬ (Prec i t c ∧ Prec i c t')

/-- An in-tree: no task has more than one immediate successor. -/
def IsInTree (i : TwoProcessorTreePrecedenceCompletionTimeInstance) : Prop :=
  ∀ t a b, ImmediatePredecessor i t a → ImmediatePredecessor i t b → a = b

/-- An out-tree: no task has more than one immediate predecessor. -/
def IsOutTree (i : TwoProcessorTreePrecedenceCompletionTimeInstance) : Prop :=
  ∀ t' a b, ImmediatePredecessor i a t' → ImmediatePredecessor i b t' → a = b

/-- Well-formedness of an instance: the parent instance is well formed (`0 < m`, positive lengths
and weights, `0 < K`), `m = 2`, all weights are equal, every listed pair names two tasks, the
listed pairs form a strict partial order, and it is an in-tree or an out-tree. -/
def WellFormed (i : TwoProcessorTreePrecedenceCompletionTimeInstance) : Prop :=
  SchedulingToMinimizeWeightedCompletionTime.WellFormed (toParent i) ∧ i.1 = 2 ∧
    (∀ p ∈ i.2.1, ∀ q ∈ i.2.1, p.2 = q.2) ∧
    (∀ p ∈ i.2.2.2, p.1 < i.2.1.length ∧ p.2 < i.2.1.length) ∧
    IsStrictOrder (Task i) (Prec i) ∧ (IsInTree i ∨ IsOutTree i)

/-- Some `m`-processor schedule (at every time at most `m` tasks run) obeys the precedence
constraints and has weighted completion time at most `K`. -/
def TwoProcessorTreePrecedenceCompletionTimeFeasible
    (i : TwoProcessorTreePrecedenceCompletionTimeInstance) : Prop :=
  ∃ σ : Task i → ℕ, (∀ u, (running (toParent i) σ u).card ≤ i.1) ∧
    (∀ t t', Prec i t t' → σ t + taskLength (toParent i) t ≤ σ t') ∧
    weightedCompletionTime (toParent i) σ ≤ i.2.2.1

open Classical in
/-- TWO-PROCESSOR TREE-PRECEDENCE SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME as a decision
problem over bitstrings. -/
noncomputable def twoProcessorTreePrecedenceCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTreePrecedenceCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTreePrecedenceCompletionTimeFeasible i)
  | none => false

/-- **TWO-PROCESSOR TREE-PRECEDENCE SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME is
NP-complete.** Source: Garey and Johnson (1979), [SS13], comment; Sethi (1977). -/
public theorem_wanted twoProcessorTreePrecedenceCompletionTime_npComplete :
    twoProcessorTreePrecedenceCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorTreePrecedenceCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorTreePrecedenceCompletionTime
