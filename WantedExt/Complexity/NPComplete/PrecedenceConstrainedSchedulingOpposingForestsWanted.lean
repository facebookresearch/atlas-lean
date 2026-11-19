/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING for opposing forests is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING (the unrestricted problem) and, in the comment to [SS11], the definitions of "in-tree"
and "out-tree" partial orders;
M. R. Garey, D. S. Johnson, R. E. Tarjan and M. Yannakakis, "Scheduling opposing forests",
SIAM Journal on Algebraic and Discrete Methods 4 (1983), 72-93, doi:10.1137/0604011.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingOpposingForests

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance Task Prec)

/-!
# PRECEDENCE CONSTRAINED SCHEDULING for opposing forests is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, a number `m ∈ ℤ⁺` of processors
(part of the input), a partial order `<` on `T` that is the disjoint union of an in-forest and an
out-forest (an "opposing forest"), and a deadline `D ∈ ℤ⁺`. QUESTION: is there an `m`-processor
schedule `σ` for `T` that meets the overall deadline `D` and obeys the precedence constraints,
i.e., such that `t < t'` implies `σ(t') ≥ σ(t) + l(t) = σ(t) + 1`?

This is the restriction of PRECEDENCE CONSTRAINED SCHEDULING
(`WantedExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingWanted`) to opposing forests.
The instance type, the tasks, the precedence relation (the list of pairs `(t, t')` with
`t < t'`), the parent well-formedness condition (unit lengths, `m > 0`, the pairs name tasks and
form a strict partial order, `D > 0`) and the question are that module's; the restriction is
added to `WellFormed`.

Following Garey and Johnson ([SS11], comment), `t` is an immediate predecessor of `t'` (and `t'`
an immediate successor of `t`) when `t < t'` and no task `c` has `t < c < t'`; an in-forest is a
partial order in which no task has more than one immediate successor, and an out-forest one in
which no task has more than one immediate predecessor. The order is the disjoint union of an
in-forest and an out-forest when the tasks split into a part `A` and its complement with no
precedence between the two parts, the order on `A` an in-forest and the order on the complement
an out-forest (either part may be empty). Since no pair crosses the split, the immediate
successors and predecessors of a task are the same in its part as in `T`. Binary encoding of
all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `t` is an immediate predecessor of `t'` (and `t'` an immediate successor of `t`): `t < t'`,
and no task `c` has `t < c < t'`. -/
def ImmediatePredecessor (i : PrecedenceConstrainedSchedulingInstance) (t t' : Task i) : Prop :=
  Prec i t t' ∧ ∀ c, ¬ (Prec i t c ∧ Prec i c t')

/-- The partial order is an opposing forest: the tasks split into a part `A` and its complement
with no precedence between the two parts, no task of `A` has more than one immediate successor
(an in-forest), and no task outside `A` has more than one immediate predecessor (an
out-forest). -/
def IsOpposingForest (i : PrecedenceConstrainedSchedulingInstance) : Prop :=
  ∃ A : Set (Task i), (∀ t t', Prec i t t' → (t ∈ A ↔ t' ∈ A)) ∧
    (∀ t ∈ A, ∀ a b, ImmediatePredecessor i t a → ImmediatePredecessor i t b → a = b) ∧
    ∀ t' ∉ A, ∀ a b, ImmediatePredecessor i a t' → ImmediatePredecessor i b t' → a = b

/-- Well-formedness of an instance: it is a well-formed PRECEDENCE CONSTRAINED SCHEDULING
instance (unit lengths, `m > 0`, the listed pairs name tasks and form a strict partial order,
`D > 0`), and the partial order is an opposing forest. -/
def WellFormed (i : PrecedenceConstrainedSchedulingInstance) : Prop :=
  PrecedenceConstrainedScheduling.WellFormed i ∧ IsOpposingForest i

open Classical in
/-- PRECEDENCE CONSTRAINED SCHEDULING for opposing forests as a decision problem over
bitstrings. -/
noncomputable def precedenceConstrainedSchedulingOpposingForestsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧
      PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingFeasible i)
  | none => false

/-- **PRECEDENCE CONSTRAINED SCHEDULING is NP-complete for opposing forests.** Source: Garey and
Johnson (1979), [SS9]; Garey, Johnson, Tarjan and Yannakakis (1983). -/
public theorem_wanted precedenceConstrainedSchedulingOpposingForests_npComplete :
    precedenceConstrainedSchedulingOpposingForestsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceConstrainedSchedulingOpposingForestsDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingOpposingForests
