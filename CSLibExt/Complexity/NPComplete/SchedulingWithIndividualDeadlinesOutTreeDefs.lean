/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING WITH INDIVIDUAL DEADLINES for out-tree precedence: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlinesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlinesOutTree

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

end MetaMathlibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlinesOutTree
