/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O|p_ij=1;r_i|ΣU_i: definitions

Source:
S. A. Kravchenko, "On the complexity of minimizing the number of late jobs in unit time open
shop", Discrete Applied Mathematics 100 (2000), 127-132, doi:10.1016/S0166-218X(99)00202-4 (the
full text was not available); recorded as strongly NP-hard (a minimal NP-hard problem) in
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classes "Open-shop
problems without preemption" and "Open-shop problems with transportation delays" (University of
Osnabrück, http://www.mathematik.uni-osnabrueck.de/research/OR/class/), problem
`O|p_ij=1;r_i|ΣU_i`, credited to Kravchenko (1999).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanDefs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopReleaseLateJobs

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan (UnitJobs)
open MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness
  (IsUnitOpenShopSchedule)

/-- An instance `(m, J, K)`: the number `m` of machines, the jobs (job `j` is the triple of its
processing times `(p_j1, …, p_jm)`, its release date `r_j` and its due date `d_j`), and the bound
`K` on the number of late jobs. -/
abbrev UnitOpenShopReleaseLateJobsInstance := ℕ × List (List ℕ × ℕ × ℕ) × ℕ

/-- The release date `r_j` of job `j`. -/
def releaseDate (i : UnitOpenShopReleaseLateJobsInstance) (j : Fin i.2.1.length) : ℕ :=
  (i.2.1.get j).2.1

/-- The due date `d_j` of job `j`. -/
def dueDate (i : UnitOpenShopReleaseLateJobsInstance) (j : Fin i.2.1.length) : ℕ :=
  (i.2.1.get j).2.2

/-- Well-formedness of an instance: `m ≥ 1`, and every job has `m` unit operations. -/
def WellFormed (i : UnitOpenShopReleaseLateJobsInstance) : Prop :=
  0 < i.1 ∧ UnitJobs i.1 (i.2.1.map Prod.fst)

/-- Some open-shop schedule of the unit operations starts no operation of a job before its
release date and has at most `K` late jobs: jobs `j` with an operation completing after `d_j`. -/
def UnitOpenShopReleaseLateJobsFeasible (i : UnitOpenShopReleaseLateJobsInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsUnitOpenShopSchedule i.1 i.2.1.length [] σ ∧
    (∀ k j, releaseDate i j ≤ σ k j) ∧
    (Finset.univ.filter fun j => ∃ k, dueDate i j < σ k j + 1).card ≤ i.2.2

open Classical in
/-- OPEN SHOP `O|p_ij=1;r_i|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def unitOpenShopReleaseLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitOpenShopReleaseLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopReleaseLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopReleaseLateJobs
