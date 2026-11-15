/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP, RELEASE DATES, UNIT TIMES, LATE JOBS (OMPT|r_i; p_ij = 1|ΣU_i) is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopReleaseLateJobs

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open UnitFlowShopPrecedenceMakespan (UnitJobs)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopSchedule)

/-!
# MPT OPEN SHOP, RELEASE DATES, UNIT TIMES, LATE JOBS (OMPT|r_i; p_ij = 1|ΣU_i) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an open shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and machine sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `1, …, n`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij`
requires every machine of `μ_j` during its processing and the operations of a job may be
processed in any order, but no two of them at the same time; a release date `r_i ∈ ℤ₀⁺`, before
which no operation of job `i` starts, and a due date `d_i ∈ ℤ₀⁺` for each job `i`; and a bound
`K`. Operations requiring a common machine cannot be processed simultaneously. QUESTION: is
there a feasible schedule in which at most `K` jobs are late, i.e. have `C_i > d_i`, where `C_i`
is the completion time of job `i` (that of its last operation)?

The MPT open shop is that of `MultiprocessorTaskOpenShopPrecedenceMakespanWanted`
(`OMPT|prec; p_ij = 1|C_max`), reused here: the stage machine sets and their well-formedness
`StagesWellFormed` (at least one stage, machine indices below `m`, pairwise different sets), the
unit-job condition `UnitJobs`, the open-shop schedule `IsMPTOpenShopSchedule` with unit
processing times (two different operations of one job, and two different operations whose
machine sets share a machine, occupy disjoint unit intervals) and the completion time
`completionTime`. Each job is listed with its processing times `(p_i1, …, p_ir)`, all equal to
`1`, and the pair `(r_i, d_i)`. The release date bounds the start of every operation of the job.
With integer data, integer start times lose no generality. Binary encoding of all numbers (the
problem is NP-complete in the strong sense).

OMPT is Brucker's stage model (*Scheduling Algorithms*, Chapter 11), as in the base module
`MultiprocessorTaskOpenShopPrecedenceMakespanWanted`: as in the MPT flow shop, every job has one
task per stage `j`, and the task of stage `j` needs the processor set `μ_j`. Brucker states the
polynomial cases of the class as `OMPT|p_ij = 1; stages = r|…`, with the number `r` of stages as a
parameter, and his algorithm for them fixes, for each order of the stages, how many jobs pass the
stages in that order, which presupposes stage-dependent sets. Task-dependent sets `μ_ij` with no
precedence between the tasks of a job, as in `MultiprocessorTaskOpenShopThreeJobsWanted`, are the
general shop with MPT without task precedences; both readings contain the classical special case
`μ_j = {M_j}` that carries the NP-hardness. A stage set may be empty, as `μ_j ⊆ {M_1, …, M_m}`
allows.

Brucker and Knust's open-shop table lists `O|p_ij = 1; r_i|∑ U_i`
(`UnitOpenShopReleaseLateJobsWanted`) as strongly NP-hard, crediting Kravchenko (dated 1999 in
their entry; the paper appeared in Discrete Applied Mathematics in 2000); it is the special case
`r = m`, `μ_j = {M_j}` of this problem. Kravchenko's paper was not available to this
formalization beyond its title.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **`OMPT|r_i; p_ij = 1|∑ U_i` is NP-complete.** Source: Kravchenko (2000); Brucker and Knust,
*Complexity results for scheduling problems*; Brucker (2004), Chapter 11. -/
public theorem_wanted multiprocessorTaskOpenShopReleaseLateJobs_npComplete :
    multiprocessorTaskOpenShopReleaseLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopReleaseLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopReleaseLateJobs
