/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING with forest precedence: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS10] RESOURCE CONSTRAINED
SCHEDULING, p. 239, comment: "If a partial order < is added, the problem becomes NP-complete in
the strong sense for r = 1, m = 2, and < a "forest."", within the entry whose reference is
[Garey and Johnson, 1975];
M. R. Garey and D. S. Johnson, "Complexity results for multiprocessor scheduling under resource
constraints", SIAM Journal on Computing 4 (1975), 397-411, doi:10.1137/0204035.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBoundDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingForestPrecedence

open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedScheduling (Task)
open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBound
  (PrecedenceResourceSchedulingInstance Prec PrecedenceWellFormed PrecedenceFeasible)

/-- `t` is an immediate predecessor of `t'` (and `t'` an immediate successor of `t`): `t < t'`,
and no task `c` has `t < c < t'`. -/
def ImmediatePredecessor (i : PrecedenceResourceSchedulingInstance) (t t' : Task i.1) : Prop :=
  Prec i t t' ∧ ∀ c, ¬ (Prec i t c ∧ Prec i c t')

/-- The partial order is a forest: no task has more than one immediate successor (an
in-forest), or no task has more than one immediate predecessor (an out-forest). -/
def IsForest (i : PrecedenceResourceSchedulingInstance) : Prop :=
  (∀ t a b, ImmediatePredecessor i t a → ImmediatePredecessor i t b → a = b) ∨
    ∀ t a b, ImmediatePredecessor i a t → ImmediatePredecessor i b t → a = b

/-- Well-formedness of an instance: it is well-formed for RESOURCE CONSTRAINED SCHEDULING with a
partial order, `m = 2`, `r = 1`, and the partial order is a forest. -/
def WellFormed (i : PrecedenceResourceSchedulingInstance) : Prop :=
  PrecedenceWellFormed i ∧ i.1.1 = 2 ∧ i.1.2.1 = 1 ∧ IsForest i

open Classical in
/-- RESOURCE CONSTRAINED SCHEDULING with forest precedence as a decision problem over
bitstrings. -/
noncomputable def resourceConstrainedSchedulingForestPrecedenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceResourceSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingForestPrecedence
