/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE TOTAL LATE WORK is NP-complete

Source:
C. N. Potts and L. N. Van Wassenhove, "Single machine scheduling to minimize total late
work", Operations Research 40 (1992), 586-595, doi:10.1287/opre.40.3.586;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS1] (the definition of a
one-processor schedule).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalLateWork

/-!
# SINGLE-MACHINE TOTAL LATE WORK is NP-complete

INSTANCE: `n` jobs to be processed on a single machine, job `j` with an integer processing
time `p_j` and an integer due date `d_j`, and an integer bound `K`. QUESTION: is there a
nonpreemptive schedule whose total late work `∑_j V_j` is at most `K`, where the late work
`V_j = min(p_j, max(0, C_j - d_j))` of job `j` completing at time `C_j` is the amount of its
processing performed after its due date?

This is the decision version of `1||ΣV_j`. Potts and Van Wassenhove (1992) prove the
nonpreemptive problem NP-hard (and give a pseudo-polynomial algorithm). Membership in NP holds
because the start times themselves are a certificate of polynomial bit length: moving jobs
earlier never increases late work, so some optimal schedule starts every job by
`n + ∑_j p_j`, and its total late work is checked with binary arithmetic. A nonpreemptive
schedule is a one-processor schedule `σ` of start times as in Garey and Johnson's [SS1]
(`IsOneProcessorSchedule` from `SequencingToMinimizeWeightedTardinessWanted`: one-to-one, and a
job starting later than another starts no earlier than the other's completion); job `j`
completes at `C_j = σ(j) + p_j`. Idle time is allowed, which does not change the question
because late work does not decrease when completion times grow. Processing times, due dates
and `K` are arbitrary nonnegative integers, so every decoded instance is well formed. Jobs are
`Fin n`, one per listed pair `(p_j, d_j)`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SINGLE-MACHINE TOTAL LATE WORK is NP-complete.** Source: Potts and Van Wassenhove
(1992). -/
public theorem_wanted totalLateWork_npComplete :
    totalLateWorkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalLateWorkDec

end MetaMathlibExt.Complexity.NPComplete.TotalLateWork
