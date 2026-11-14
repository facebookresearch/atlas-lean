/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING WITH INDIVIDUAL DEADLINES for out-tree precedence is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS11] SCHEDULING WITH INDIVIDUAL
DEADLINES, comment: remains NP-complete even if `<` is an "out-tree" partial order (no task has
more than one immediate predecessor);
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SchedulingWithIndividualDeadlinesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlinesOutTree

/-!
# SCHEDULING WITH INDIVIDUAL DEADLINES for out-tree precedence is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, a number `m ∈ ℤ⁺` of processors, a
partial order `<` on `T` that is an "out-tree" partial order (no task has more than one
immediate predecessor), and for each task `t ∈ T` a deadline `d(t) ∈ ℤ⁺`. QUESTION: is there an
`m`-processor schedule `σ` for `T` that obeys the precedence constraints and meets all the
deadlines, i.e., `σ(t) + l(t) ≤ d(t)` for all `t ∈ T`?

This is the restriction of SCHEDULING WITH INDIVIDUAL DEADLINES
(`WantedExt.Complexity.NPComplete.SchedulingWithIndividualDeadlinesWanted`) to out-tree partial
orders. The instance type, the precedence relation, the parent well-formedness condition and the
question are that module's
(`SchedulingWithIndividualDeadlines.SchedulingWithIndividualDeadlinesInstance`,
`SchedulingWithIndividualDeadlines.Prec`, `SchedulingWithIndividualDeadlines.WellFormed`,
`SchedulingWithIndividualDeadlines.SchedulingWithIndividualDeadlinesFeasible`); the restriction
is added to `WellFormed`. The out-tree condition is the source's parenthetical definition: `t` is
an immediate predecessor of `t'` when `t < t'` and no task `c` has `t < c < t'`, and every task
has at most one immediate predecessor. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `t` is an immediate predecessor of `t'`: `t < t'`, and no task `c` has `t < c < t'`. -/
def ImmediatePredecessor
    (i : SchedulingWithIndividualDeadlines.SchedulingWithIndividualDeadlinesInstance)
    (t t' : SchedulingWithIndividualDeadlines.Task i) : Prop :=
  SchedulingWithIndividualDeadlines.Prec i t t' ∧
    ∀ c, ¬ (SchedulingWithIndividualDeadlines.Prec i t c ∧
      SchedulingWithIndividualDeadlines.Prec i c t')

/-- Well-formedness of an instance: it is a well-formed SCHEDULING WITH INDIVIDUAL DEADLINES
instance (`0 < m`, listed pairs name tasks and form a strict partial order, positive deadlines),
and no task has more than one immediate predecessor. -/
def WellFormed (i : SchedulingWithIndividualDeadlines.SchedulingWithIndividualDeadlinesInstance) :
    Prop :=
  SchedulingWithIndividualDeadlines.WellFormed i ∧
    ∀ t' a b, ImmediatePredecessor i a t' → ImmediatePredecessor i b t' → a = b

open Classical in
/-- SCHEDULING WITH INDIVIDUAL DEADLINES for out-tree precedence as a decision problem over
bitstrings. -/
noncomputable def schedulingWithIndividualDeadlinesOutTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SchedulingWithIndividualDeadlines.SchedulingWithIndividualDeadlinesInstance) x with
  | some i => decide (WellFormed i ∧
      SchedulingWithIndividualDeadlines.SchedulingWithIndividualDeadlinesFeasible i)
  | none => false

/-- **SCHEDULING WITH INDIVIDUAL DEADLINES is NP-complete for out-tree precedence.** Source:
Garey and Johnson (1979), [SS11], comment; Brucker, Garey and Johnson (1977). -/
public theorem_wanted schedulingWithIndividualDeadlinesOutTree_npComplete :
    schedulingWithIndividualDeadlinesOutTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L schedulingWithIndividualDeadlinesOutTreeDec

end MetaMathlibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlinesOutTree
