/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL MACHINES WITH IN-TREE AND RELEASE DATES (P|intree; r_i; p_i = 1|C_max): definitions

Source:
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2(3)
(1977), 275-284, doi:10.1287/moor.2.3.275;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Parallel machine problems without
preemption", which lists `P|intree; r_i; p_i = 1|C_max` as minimal NP-hard in the strong sense
with the attribution to Brucker, Garey and Johnson (1977);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 1 (notation) and
Section 5.2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingOpposingForestsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelMachinesInTreeReleaseMakespan

open PrecedenceConstrainedScheduling (PrecedenceConstrainedSchedulingInstance Task taskLength
  Prec running)
open PrecedenceConstrainedSchedulingOpposingForests (ImmediatePredecessor)

/-- An instance: a PRECEDENCE CONSTRAINED SCHEDULING instance (processing times, all `1`; the
number `m` of machines; the pairs `(t, t')` with `t → t'`; the bound `K`) and the release dates,
job `t` having the `t`-th listed release date `r_t`. -/
abbrev ParallelMachinesInTreeReleaseMakespanInstance :=
  PrecedenceConstrainedSchedulingInstance × List ℕ

/-- The release date `r_t` of job `t`. -/
def releaseDate (i : ParallelMachinesInTreeReleaseMakespanInstance) (t : Task i.1) : ℕ :=
  i.2.getD t 0

/-- Well-formedness of an instance: it is a well-formed PRECEDENCE CONSTRAINED SCHEDULING
instance (unit processing times, `m > 0`, the listed pairs name jobs and form a strict partial
order, `K > 0`), there is one release date per job, and the precedence relation is an in-tree:
no job has more than one immediate successor. -/
def WellFormed (i : ParallelMachinesInTreeReleaseMakespanInstance) : Prop :=
  PrecedenceConstrainedScheduling.WellFormed i.1 ∧ i.2.length = i.1.1.length ∧
    ∀ t a b, ImmediatePredecessor i.1 t a → ImmediatePredecessor i.1 t b → a = b

/-- Some schedule of the unit-time jobs on `m` machines respects the release dates and the
precedence constraints and has makespan at most `K`. -/
def ParallelMachinesInTreeReleaseMakespanFeasible
    (i : ParallelMachinesInTreeReleaseMakespanInstance) : Prop :=
  ∃ σ : Task i.1 → ℕ, (∀ u, (running i.1 σ u).card ≤ i.1.2.1) ∧
    (∀ t, releaseDate i t ≤ σ t) ∧
    (∀ t t', Prec i.1 t t' → σ t + taskLength i.1 t ≤ σ t') ∧
    ∀ t, σ t + taskLength i.1 t ≤ i.1.2.2.2

open Classical in
/-- `P|intree; r_i; p_i = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def parallelMachinesInTreeReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ParallelMachinesInTreeReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ ParallelMachinesInTreeReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ParallelMachinesInTreeReleaseMakespan
