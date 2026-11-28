/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP, TREE PRECEDENCE, RELEASE DATES (FMPT|tree; r_i; p_ij = 1|C_max): definitions

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT|tree; r_i; p_ij = 1|C_max` as minimal NP-hard in the strong sense with
the attribution to Brucker and Knust (1999);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (the MPT flow-shop
model) and Section 1.3 (precedence relations).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open UnitFlowShopPrecedenceMakespan (PrecWellFormed UnitJobs)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTPrecedenceSchedule)
open MultiprocessorTaskFlowShopTreeLateness (IsTreePrecedence)

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, the jobs
(job `i` listed by its processing times `(p_i1, …, p_ir)` and its release date `r_i`), the arcs
`(i, k)` with `i → k`, and the bound `K`. -/
abbrev MultiprocessorTaskFlowShopTreeReleaseMakespanInstance :=
  ℕ × List (List ℕ) × List (List ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The release date `r_j` of job `j`. -/
def releaseDate (i : MultiprocessorTaskFlowShopTreeReleaseMakespanInstance)
    (j : Fin i.2.2.1.length) : ℕ :=
  (i.2.2.1.get j).2

/-- Well-formedness of an instance: the machine environment is well formed
(`StagesWellFormed`), every stage needs at least one processor (each stage's processor list is
nonempty), every job has `r` unit processing times (`UnitJobs`), the listed arcs
describe an acyclic precedence digraph on the jobs (`PrecWellFormed`), and its
precedence relation is an in-forest or an out-forest, not necessarily connected
(`IsTreePrecedence`). -/
def WellFormed (i : MultiprocessorTaskFlowShopTreeReleaseMakespanInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ (∀ M ∈ i.2.1, M ≠ []) ∧
    UnitJobs i.2.1.length (i.2.2.1.map Prod.fst) ∧
    PrecWellFormed i.2.2.1.length i.2.2.2.1 ∧ IsTreePrecedence i.2.2.1.length i.2.2.2.1

/-- Some MPT flow-shop schedule of the unit-time jobs obeys the precedence constraints, starts no
operation of job `j` before `r_j`, and has makespan at most `K`. -/
def MultiprocessorTaskFlowShopTreeReleaseMakespanFeasible
    (i : MultiprocessorTaskFlowShopTreeReleaseMakespanInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧ (∀ j s, releaseDate i j ≤ σ j s) ∧
      ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `FMPT|tree; r_i; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskFlowShopTreeReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskFlowShopTreeReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskFlowShopTreeReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeReleaseMakespan
