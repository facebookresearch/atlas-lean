/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH TWO PROCESSORS AND RELEASE DATES (OMPT2|r_i|C_max) is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks" (`OMPT2|r_i|C_max`, minimal NP-hard in the strong sense, credited to Lawler, Lenstra, and
Rinnooy Kan 1981, 1982);
E. L. Lawler, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Minimizing maximum lateness in a
two-machine open shop", Mathematics of Operations Research 6 (1981), 153-158,
doi:10.1287/moor.6.1.153; Erratum, Mathematics of Operations Research 7 (1982), 635,
doi:10.1287/moor.7.4.635 (the two-machine open shop, the case `μ_j = {M_j}`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (the MPT open-shop
model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesTotalCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance Job Stage
  processingTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopSchedule)

/-!
# MPT OPEN SHOP WITH TWO PROCESSORS AND RELEASE DATES (OMPT2|r_i|C_max) is NP-complete

INSTANCE: two processors `M_1, M_2`; an open shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and processor sets `μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `1, …, n` with
`n ≥ 1`, each consisting of `r` tasks `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`, where
`O_ij` requires every processor of `μ_j` during its processing; a release date `r_i ∈ ℤ₀⁺` for
each job `i` (no task of `i` starts before `r_i`); and a bound `K`. Tasks requiring a common
processor cannot be processed simultaneously, and no two tasks of the same job can be processed
simultaneously; the tasks of a job may be processed in any order. QUESTION: is there a feasible
schedule with makespan `max_i C_i ≤ K`, where `C_i` is the completion time of job `i` (that of
its last task)?

The machine environment, jobs and bound are an `OMPT2||ΣC_i` instance
(`MultiprocessorTaskOpenShopTwoMachinesTotalCompletionWanted`, whose well-formedness is reused:
two processors, well-formed stage processor sets, one processing time per stage for each job,
at least one job), with the release dates listed one per job. Its MPT open-shop schedule
`IsMPTOpenShopSchedule` (from `MultiprocessorTaskOpenShopPrecedenceMakespanWanted`: task
`(i, s)` gets a start time `σ i s` and occupies the half-open interval `[σ i s, σ i s + p_is)` on
every processor of `μ_s`; two different tasks of the same job, or two different tasks whose
processor sets share a processor, occupy disjoint intervals), its accessors (`Job`, `Stage`,
`processingTime`) and `completionTime` are reused as well, after Brucker's MPT model
(*Scheduling Algorithms*, 5th ed., Chapter 11).

Brucker and Knust record `OMPT2|r_i|C_max` as minimal NP-hard in the strong sense with the
attribution to Lawler, Lenstra, and Rinnooy Kan (1981, with their 1982 erratum), who show that the
two-machine open shop `O2||L_max` is NP-hard; reversing time turns due dates into release dates, so
`O2|r_i|C_max` is NP-hard as well, and it is the case `r = 2`, `μ_1 = {M_1}`, `μ_2 = {M_2}` of this
problem. NP membership: in a yes-instance every start time is at most `K`, so start times are a
certificate of polynomial size in the binary input, checked in polynomial time. With integer data,
integer start times lose no generality. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: an `OMPT2||ΣC_i` instance (the number of processors, the stage processor sets,
one list of `r` processing times per job, the bound `K`) and the release dates, job `j` having
the `j`-th listed release date `r_j`. -/
abbrev MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanInstance :=
  MultipurposeFlowShopThreeJobsInstance × List ℕ

/-- Well-formedness of an instance: a well-formed `OMPT2||ΣC_i` instance with one release date
per job. -/
def WellFormed (i : MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanInstance) : Prop :=
  MultiprocessorTaskOpenShopTwoMachinesTotalCompletion.WellFormed i.1 ∧
    i.2.length = i.1.2.2.1.length

/-- Some MPT open-shop schedule of the jobs starts no task of job `j` before `r_j` and has
makespan at most `K`. -/
def MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanFeasible
    (i : MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanInstance) : Prop :=
  ∃ σ : Job i.1 → Stage i.1 → ℕ, IsMPTOpenShopSchedule i.1.2.1 (processingTime i.1) σ ∧
    (∀ (j : Job i.1) s, i.2.getD j 0 ≤ σ j s) ∧
      ∀ j, completionTime (processingTime i.1) σ j ≤ i.1.2.2.2

open Classical in
/-- `OMPT2|r_i|C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopTwoMachinesReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultiprocessorTaskOpenShopTwoMachinesReleaseMakespanFeasible i)
  | none => false

/-- **`OMPT2|r_i|C_max` is NP-complete.** Source: Brucker and Knust, *Complexity results for
scheduling problems*; Lawler, Lenstra, and Rinnooy Kan (1981, 1982); Brucker (2007),
Chapter 11. -/
public theorem_wanted multiprocessorTaskOpenShopTwoMachinesReleaseMakespan_npComplete :
    multiprocessorTaskOpenShopTwoMachinesReleaseMakespanDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopTwoMachinesReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesReleaseMakespan
