/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING on 2 dedicated processors: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING, p. 239 (comment: "If each task `t` can only be executed by a specified processor
`p(t)`, the problem is NP-complete for `m = 2` and `<` arbitrary, and for `m` arbitrary and `<` a
forest, but can be solved in polynomial time for `m` arbitrary if `<` is a 'cyclic forest'
[Goyal, 1976]"), citing D. K. Goyal, "Scheduling processor bound systems", Technical Report,
Computer Science Department, Washington State University (1976) (not available to this
formalization).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceScheduling

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance Task taskLength Prec running)

/-- An instance: a PRECEDENCE CONSTRAINED SCHEDULING instance and the processors `p(t)` of the
tasks, task `t` being the `t`-th entry. -/
abbrev DedicatedProcessorsInstance := PrecedenceConstrainedSchedulingInstance × List ℕ

/-- The processor `p(t)` of task `t`. -/
def processor (i : DedicatedProcessorsInstance) (t : Task i.1) : ℕ :=
  i.2.getD t 0

/-- Well-formedness for any number `m` of processors: the parent's (unit lengths, `m > 0`, the
listed pairs name tasks and form a strict partial order, `D > 0`), one processor per task, and
every processor below `m`. -/
def DedicatedWellFormed (i : DedicatedProcessorsInstance) : Prop :=
  PrecedenceConstrainedScheduling.WellFormed i.1 ∧ i.2.length = i.1.1.length ∧
    ∀ q ∈ i.2, q < i.1.2.1

/-- Some `m`-processor schedule meets the overall deadline `D`, obeys the precedence
constraints, and runs any two different tasks with the same processor in disjoint intervals. -/
def DedicatedProcessorsFeasible (i : DedicatedProcessorsInstance) : Prop :=
  ∃ σ : Task i.1 → ℕ, (∀ u, (running i.1 σ u).card ≤ i.1.2.1) ∧
    (∀ t, σ t + taskLength i.1 t ≤ i.1.2.2.2) ∧
    (∀ t t', Prec i.1 t t' → σ t + taskLength i.1 t ≤ σ t') ∧
    ∀ t t', t ≠ t' → processor i t = processor i t' →
      σ t + taskLength i.1 t ≤ σ t' ∨ σ t' + taskLength i.1 t' ≤ σ t

/-- Well-formedness of an instance: `DedicatedWellFormed` with `m = 2`. -/
def WellFormed (i : DedicatedProcessorsInstance) : Prop :=
  DedicatedWellFormed i ∧ i.1.2.1 = 2

open Classical in
/-- PRECEDENCE CONSTRAINED SCHEDULING on 2 dedicated processors as a decision problem over
bitstrings. -/
noncomputable def twoDedicatedProcessorPrecedenceSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := DedicatedProcessorsInstance) x with
  | some i => decide (WellFormed i ∧ DedicatedProcessorsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceScheduling
