/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP, RELEASE DATES, UNIT TIMES, LATE JOBS (OMPT|r_i; p_ij = 1|ΣU_i): definitions

Source:
S. A. Kravchenko, "On the complexity of minimizing the number of late jobs in unit time open
shop", Discrete Applied Mathematics 100 (2000), 127-132, doi:10.1016/S0166-218X(99)00202-4;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT|r_i; p_ij = 1|∑ U_i` as minimal NP-hard in the strong sense with the
attribution to Kravchenko (1999);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (the MPT open-shop
model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopReleaseLateJobs

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open UnitFlowShopPrecedenceMakespan (UnitJobs)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopSchedule)

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, the jobs
(job `i` listed by its processing times `(p_i1, …, p_ir)` and the pair `(r_i, d_i)` of release
date and due date), and the bound `K`. -/
abbrev MultiprocessorTaskOpenShopReleaseLateJobsInstance :=
  ℕ × List (List ℕ) × List (List ℕ × (ℕ × ℕ)) × ℕ

/-- The release date `r_i` of job `i`. -/
def releaseDate (i : MultiprocessorTaskOpenShopReleaseLateJobsInstance)
    (j : Fin i.2.2.1.length) : ℕ :=
  (i.2.2.1.get j).2.1

/-- The due date `d_i` of job `i`. -/
def dueDate (i : MultiprocessorTaskOpenShopReleaseLateJobsInstance)
    (j : Fin i.2.2.1.length) : ℕ :=
  (i.2.2.1.get j).2.2

/-- Well-formedness of an instance: the machine environment is well formed
(`StagesWellFormed`), and every job has `r` unit processing times (`UnitJobs`). -/
def WellFormed (i : MultiprocessorTaskOpenShopReleaseLateJobsInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ UnitJobs i.2.1.length (i.2.2.1.map Prod.fst)

/-- Some MPT open-shop schedule of the unit-time jobs starts no operation of a job before its
release date and has at most `K` late jobs (`d_j < C_j`). -/
def MultiprocessorTaskOpenShopReleaseLateJobsFeasible
    (i : MultiprocessorTaskOpenShopReleaseLateJobsInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTOpenShopSchedule i.2.1 (fun _ _ => 1) σ ∧ (∀ j s, releaseDate i j ≤ σ j s) ∧
      (Finset.univ.filter fun j => dueDate i j < completionTime (fun _ _ => 1) σ j).card ≤
        i.2.2.2

open Classical in
/-- `OMPT|r_i; p_ij = 1|∑ U_i` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopReleaseLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskOpenShopReleaseLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopReleaseLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopReleaseLateJobs
