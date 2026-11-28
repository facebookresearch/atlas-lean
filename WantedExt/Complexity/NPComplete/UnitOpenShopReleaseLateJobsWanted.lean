/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O|p_ij=1;r_i|ΣU_i is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import WantedExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanWanted
public import WantedExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopReleaseLateJobs

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan (UnitJobs)
open MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness
  (IsUnitOpenShopSchedule)

/-!
# OPEN SHOP O|p_ij=1;r_i|ΣU_i is NP-complete

INSTANCE: an open shop with `m` machines `M_1, …, M_m` (`m` part of the input) and jobs
`1, …, n`, each consisting of `m` operations of unit length, `O_ij` processed on `M_j`, in any
order but no two at the same time; each machine processes at most one operation at a time; for
each job `i` a release date `r_i ∈ ℤ₀⁺` (no operation of `i` starts before `r_i`) and a due date
`d_i ∈ ℤ₀⁺`; a bound `K`. QUESTION: is there a schedule in which at most `K` jobs are late, a job
`i` being late when its completion time `C_i` (that of its last operation) exceeds `d_i`?

This is Brucker and Knust's `O|p_ij=1;r_i|ΣU_i`, listed as minimal strongly NP-hard and credited
to Kravchenko. Each job is listed with its processing times, all `1` (one per machine, so the
input lists all `n · m` operations, as in `UnitOpenShopOutTreeMaxLatenessWanted`), its release
date and its due date; `WellFormed` requires `m ≥ 1` and unit jobs
(`UnitFlowShopPrecedenceMakespan.UnitJobs`). A schedule gives operation `O_jk` the start time
`σ k j ∈ ℕ` and is `UnitOpenShopOutTreeMaxLateness.IsUnitOpenShopSchedule` with no precedence
arcs: the operations on one machine, and the operations of one job, start at pairwise different
times, i.e. do not overlap. Integer start times lose nothing: rounding every start time of a
feasible schedule down keeps unit operations that did not overlap apart, keeps every operation
at or after its integer release date, and completes no operation later. Job `j` is late when
some operation of `j` completes after `d_j`. Binary encoding of all numbers. Membership in NP:
the `n · m` start times are a certificate (some optimal schedule starts every operation before
`max_j r_j + n · m`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **OPEN SHOP `O|p_ij=1;r_i|ΣU_i` is NP-complete.** Source: Kravchenko (2000), as recorded in
the Brucker-Knust classification of scheduling problems. -/
public theorem_wanted unitOpenShopReleaseLateJobs_npComplete :
    unitOpenShopReleaseLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitOpenShopReleaseLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopReleaseLateJobs
