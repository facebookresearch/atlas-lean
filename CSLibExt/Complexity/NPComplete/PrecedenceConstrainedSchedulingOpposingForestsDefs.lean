/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING for opposing forests: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING (the unrestricted problem) and, in the comment to [SS11], the definitions of "in-tree"
and "out-tree" partial orders;
M. R. Garey, D. S. Johnson, R. E. Tarjan and M. Yannakakis, "Scheduling opposing forests",
SIAM Journal on Algebraic and Discrete Methods 4 (1983), 72-93, doi:10.1137/0604011.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingOpposingForests

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance Task Prec)

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

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingOpposingForests
