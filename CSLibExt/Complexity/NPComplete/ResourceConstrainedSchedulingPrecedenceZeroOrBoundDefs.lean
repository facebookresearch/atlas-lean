/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING with precedence and 0-or-B requirements: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS10] RESOURCE CONSTRAINED
SCHEDULING, p. 239, comment: "If each resource requirement is restricted to be either 0 or
B_i, the problem is NP-complete for m = 2, r = 1, and < arbitrary [Ullman, 1976]";
J. D. Ullman, "Complexity of sequencing problems", in E. G. Coffman, Jr. (ed.), *Computer and
Job/Shop Scheduling Theory*, John Wiley & Sons, New York (1976), 139-164.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ResourceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBound

open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedScheduling
  (ResourceConstrainedSchedulingInstance Task req bound running)

/-- An instance of RESOURCE CONSTRAINED SCHEDULING with a partial order: a RESOURCE
CONSTRAINED SCHEDULING instance and the list of the pairs `(t, t')` with `t < t'`. -/
abbrev PrecedenceResourceSchedulingInstance :=
  ResourceConstrainedSchedulingInstance × List (ℕ × ℕ)

/-- The precedence relation: `t < t'` when the pair `(t, t')` is listed. -/
def Prec (i : PrecedenceResourceSchedulingInstance) (t t' : Task i.1) : Prop :=
  ((t : ℕ), (t' : ℕ)) ∈ i.2

/-- Well-formedness of RESOURCE CONSTRAINED SCHEDULING with a partial order: the
RESOURCE CONSTRAINED SCHEDULING instance is well-formed (`0 < m`, `0 < r`, `r` positive bounds,
rows of length `r` with `R_k(t) ≤ B_k`, `0 < D`), every listed pair names two tasks, and the
listed pairs form a strict partial order. -/
def PrecedenceWellFormed (i : PrecedenceResourceSchedulingInstance) : Prop :=
  ResourceConstrainedScheduling.WellFormed i.1 ∧
    (∀ p ∈ i.2, p.1 < i.1.2.2.2.1.length ∧ p.2 < i.1.2.2.2.1.length) ∧
    IsStrictOrder (Task i.1) (Prec i)

/-- Some `m`-processor schedule of the unit-length tasks meets the deadline, obeys the
precedence constraints and, at every time, keeps the total requirement of the running tasks
within each resource bound. -/
def PrecedenceFeasible (i : PrecedenceResourceSchedulingInstance) : Prop :=
  ∃ σ : Task i.1 → ℕ, (∀ t, σ t + 1 ≤ i.1.2.2.2.2) ∧
    (∀ u, (running i.1 σ u).card ≤ i.1.1) ∧
    (∀ t t', Prec i t t' → σ t + 1 ≤ σ t') ∧
    ∀ u, ∀ k < i.1.2.1, ∑ t ∈ running i.1 σ u, req i.1 t k ≤ bound i.1 k

/-- Well-formedness of an instance: it is well-formed for RESOURCE CONSTRAINED SCHEDULING with a
partial order, `m = 2`, `r = 1`, and every task requires either `0` or all `B_1` of the
resource. -/
def WellFormed (i : PrecedenceResourceSchedulingInstance) : Prop :=
  PrecedenceWellFormed i ∧ i.1.1 = 2 ∧ i.1.2.1 = 1 ∧
    ∀ t : Task i.1, req i.1 t 0 = 0 ∨ req i.1 t 0 = bound i.1 0

open Classical in
/-- RESOURCE CONSTRAINED SCHEDULING with precedence and 0-or-B requirements as a decision
problem over bitstrings. -/
noncomputable def resourceConstrainedSchedulingPrecedenceZeroOrBoundDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceResourceSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBound
