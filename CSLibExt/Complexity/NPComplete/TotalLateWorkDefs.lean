/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE TOTAL LATE WORK: definitions

Source:
C. N. Potts and L. N. Van Wassenhove, "Single machine scheduling to minimize total late
work", Operations Research 40 (1992), 586-595, doi:10.1287/opre.40.3.586;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS1] (the definition of a
one-processor schedule).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalLateWork

/-- An instance: the jobs, job `j` being the `j`-th pair `(p_j, d_j)` of processing time and
due date, and the bound `K`. -/
abbrev TotalLateWorkInstance := List (ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed pairs. -/
abbrev Job (i : TotalLateWorkInstance) : Type := Fin i.1.length

/-- The processing time `p_j` of job `j`. -/
def processingTime (i : TotalLateWorkInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The due date `d_j` of job `j`. -/
def dueDate (i : TotalLateWorkInstance) (j : Job i) : ℕ :=
  (i.1.get j).2

/-- The late work `V_j = min(p_j, max(0, C_j - d_j))` of job `j` when it completes at time `C`
(natural-number subtraction is `max(0, C - d_j)`). -/
def lateWork (i : TotalLateWorkInstance) (j : Job i) (C : ℕ) : ℕ :=
  min (processingTime i j) (C - dueDate i j)

/-- Some one-processor schedule `σ` (start times) has total late work
`∑ j, V_j` at most `K`, where job `j` completes at `σ(j) + p_j`. -/
def TotalLateWorkFeasible (i : TotalLateWorkInstance) : Prop :=
  ∃ σ : Job i → ℕ,
    SequencingToMinimizeWeightedTardiness.IsOneProcessorSchedule (processingTime i) σ ∧
      ∑ j, lateWork i j (σ j + processingTime i j) ≤ i.2

open Classical in
/-- SINGLE-MACHINE TOTAL LATE WORK as a decision problem over bitstrings. -/
noncomputable def totalLateWorkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TotalLateWorkInstance) x with
  | some i => decide (TotalLateWorkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TotalLateWork
