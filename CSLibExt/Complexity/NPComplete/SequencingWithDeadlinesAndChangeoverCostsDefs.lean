/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING WITH DEADLINES AND CHANGEOVER COSTS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS6] SEQUENCING WITH DEADLINES AND
SET-UP TIMES, p. 238 (comment: "The related problem in which set-up times are replaced by
'changeover costs,' and we want to know if there is a schedule that meets all the deadlines and
has total changeover cost at most `K`, is NP-complete even if all changeover costs are equal");
J. Bruno and P. Downey, "Complexity of task sequencing with deadlines, set-up times and
changeover costs", SIAM Journal on Computing 7 (1978), 393-404, doi:10.1137/0207031.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.SequencingWithDeadlinesAndSetUpTimesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingWithDeadlinesAndChangeoverCosts

open MetaMathlibExt.Complexity.NPComplete.SequencingWithDeadlinesAndSetUpTimes
  (SequencingWithDeadlinesAndSetUpTimesInstance Task taskLength deadline compiler
    IsOneProcessorSchedule)

/-- An instance: the changeover costs of the compilers and the tasks (in the shape of the
parent's instance), and the bound `K`. -/
abbrev SequencingWithDeadlinesAndChangeoverCostsInstance :=
  SequencingWithDeadlinesAndSetUpTimesInstance × ℕ

/-- The changeover cost `γ(c)` of compiler `c`. -/
def changeoverCost (i : SequencingWithDeadlinesAndChangeoverCostsInstance) (c : ℕ) : ℕ :=
  i.1.1.getD c 0

/-- Under `σ`, task `t` directly precedes task `t'` and has a different compiler. -/
def ChangeoverBefore (i : SequencingWithDeadlinesAndChangeoverCostsInstance)
    (σ : Task i.1 → ℕ) (t t' : Task i.1) : Prop :=
  σ t < σ t' ∧ (∀ t'', ¬ (σ t < σ t'' ∧ σ t'' < σ t')) ∧ compiler i.1 t ≠ compiler i.1 t'

open Classical in
/-- The total changeover cost of `σ`: the changeover cost of `k(t')` for every task `t'` whose
direct predecessor has a different compiler. -/
noncomputable def totalChangeoverCost (i : SequencingWithDeadlinesAndChangeoverCostsInstance)
    (σ : Task i.1 → ℕ) : ℕ :=
  ∑ t', if ∃ t, ChangeoverBefore i σ t t' then changeoverCost i (compiler i.1 t') else 0

/-- Well-formedness of an instance: the parent's (every task has a positive length, a positive
deadline, and a compiler in `C`). -/
def WellFormed (i : SequencingWithDeadlinesAndChangeoverCostsInstance) : Prop :=
  SequencingWithDeadlinesAndSetUpTimes.WellFormed i.1

/-- Some one-processor schedule meets every deadline and has total changeover cost at most
`K`. -/
def SequencingWithDeadlinesAndChangeoverCostsFeasible
    (i : SequencingWithDeadlinesAndChangeoverCostsInstance) : Prop :=
  ∃ σ : Task i.1 → ℕ, IsOneProcessorSchedule (taskLength i.1) σ ∧
    (∀ t, σ t + taskLength i.1 t ≤ deadline i.1 t) ∧ totalChangeoverCost i σ ≤ i.2

open Classical in
/-- SEQUENCING WITH DEADLINES AND CHANGEOVER COSTS as a decision problem over bitstrings. -/
noncomputable def sequencingWithDeadlinesAndChangeoverCostsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SequencingWithDeadlinesAndChangeoverCostsInstance) x with
  | some i => decide (WellFormed i ∧ SequencingWithDeadlinesAndChangeoverCostsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SequencingWithDeadlinesAndChangeoverCosts
