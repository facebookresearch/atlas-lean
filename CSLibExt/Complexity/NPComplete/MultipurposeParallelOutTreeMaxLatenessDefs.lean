/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE PARALLEL SCHEDULING WITH OUT-TREE PRECEDENCE AND UNIT TIMES TO MINIMIZE: definitions
MAXIMUM LATENESS is NP-complete

Source:
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines) and Table 5.3 (`P|pᵢ = 1; outtree|L_max`, NP-hard in
the strong sense, Brucker et al.).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLatenessDefs
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelOutTreeMaxLateness

open MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule MPMWellFormed)
open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)
open MultiprocessorTaskFlowShopTreeLateness (ImmediatePredecessor)

/-- An instance: an MPM job-shop instance (`m`, the jobs as lists of operations `(pᵢ, μᵢ)`, an
unused bound slot), the precedence arcs `(i, k)`, the due dates (the `i`-th for job `i`), and the
bound `y` as a pair `(y⁺, y⁻)` with `y = y⁺ - y⁻`. -/
abbrev MultipurposeParallelOutTreeMaxLatenessInstance :=
  MPMJobShopInstance × List (ℕ × ℕ) × List ℕ × (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed MPM job-shop instance (machines `1, …, m`,
nonempty machine sets) with at least one job, every job having exactly one operation, of
processing time `1`, and an unused bound slot `0`; one due date per job; arcs that name jobs and
form an acyclic digraph; and an out-forest (every job has at most one immediate predecessor). -/
def WellFormed (i : MultipurposeParallelOutTreeMaxLatenessInstance) : Prop :=
  MPMWellFormed i.1.1 i.1 ∧ i.1.2.1 ≠ [] ∧
    (∀ job ∈ i.1.2.1, job.length = 1 ∧ ∀ o ∈ job, o.1 = 1) ∧ i.1.2.2 = 0 ∧
    i.2.2.1.length = i.1.2.1.length ∧ PrecWellFormed i.1.2.1.length i.2.1 ∧
    ∀ k a b : Fin i.1.2.1.length, ImmediatePredecessor i.2.1 a k →
      ImmediatePredecessor i.2.1 b k → a = b

/-- Some MPM schedule of the jobs obeys the precedence arcs and completes every job `j` with
lateness `Cⱼ - dⱼ ≤ y⁺ - y⁻`. -/
def MultipurposeParallelOutTreeMaxLatenessFeasible
    (i : MultipurposeParallelOutTreeMaxLatenessInstance) : Prop :=
  ∃ a σ : Operation i.1 → ℕ, IsMPMJobShopSchedule i.1 a σ ∧
    (∀ t t' : Operation i.1, Prec i.2.1 t.1 t'.1 → σ t + opLength i.1 t ≤ σ t') ∧
    ∀ t, σ t + opLength i.1 t + i.2.2.2.2 ≤ i.2.2.1.getD t.1 0 + i.2.2.2.1

open Classical in
/-- `PMPM|outtree; pᵢ = 1|L_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelOutTreeMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelOutTreeMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelOutTreeMaxLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelOutTreeMaxLateness
