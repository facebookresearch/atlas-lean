/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH TWO PROCESSORS, MAXIMUM LATENESS (OMPT2||L_max) is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks" (`OMPT2||L_max`, minimal NP-hard in the strong sense, credited to Lawler, Lenstra, and
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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesMaximumLatenessWanted
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesMaximumLateness

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeOpenShopTwoMachinesMaximumLateness
  (MultipurposeOpenShopTwoMachinesMaximumLatenessInstance Job Stage processingTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopSchedule)

/-!
# MPT OPEN SHOP WITH TWO PROCESSORS, MAXIMUM LATENESS (OMPT2||L_max) is NP-complete

INSTANCE: two processors `M_1, M_2`; an open shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and processor sets `μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `1, …, n` with
`n ≥ 1`, each consisting of `r` tasks `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`, where
`O_ij` requires every processor of `μ_j` during its processing; a due date `d_i ∈ ℤ₀⁺` for each
job `i`; and a bound `y ∈ ℤ`. Tasks requiring a common processor cannot be processed
simultaneously, and no two tasks of the same job can be processed simultaneously; the tasks of a
job may be processed in any order. QUESTION: is there a feasible schedule with maximum lateness
`max_i (C_i - d_i) ≤ y`, where `C_i` is the completion time of job `i` (that of its last task)?

The instance shape and its accessors (`Job`, `Stage`, `processingTime`) are those of
`OMPM2||L_max` (`MultipurposeOpenShopTwoMachinesMaximumLatenessWanted`): the stage processor
sets, one list of `r` processing times per job, the due dates (job `j` has the `j`-th listed due
date), and `y` as a pair `(y⁺, y⁻)` with `y = y⁺ - y⁻`, so `C_j - d_j ≤ y` reads
`C_j + y⁻ ≤ d_j + y⁺`. Its well-formedness is that module's without the condition that every
machine set be nonempty, which belongs to the multipurpose-machine model (an MPM operation runs
on one machine of its set); an MPT processor set may be empty, as `μ_j ⊆ {M_1, M_2}` allows, and
tasks of such a stage conflict only with the other tasks of their job. `StagesWellFormed` (at
least one stage, processor indices below `2`, pairwise different sets compared as `Finset`s) and
`completionTime` are those of `MultipurposeFlowShopPrecedenceMakespanWanted`. The MPT open-shop
schedule `IsMPTOpenShopSchedule` (task `(i, s)` gets a start time `σ i s` and occupies the
half-open interval `[σ i s, σ i s + p_is)` on every processor of `μ_s`; two different tasks of
the same job, or two different tasks whose processor sets share a processor, occupy disjoint
intervals) is that of `OMPT|prec; p_ij = 1|C_max`
(`MultiprocessorTaskOpenShopPrecedenceMakespanWanted`), after Brucker's MPT model (*Scheduling
Algorithms*, 5th ed., Chapter 11: "open shop problems with MPT are defined as flow shop problems
with MPT but without precedence constraints between tasks. However, no pair of tasks of the same
job can be processed simultaneously").

The two-machine open shop `O2||L_max` of Lawler, Lenstra, and Rinnooy Kan (1981, with their 1982
erratum) is the case `r = 2`, `μ_1 = {M_1}`, `μ_2 = {M_2}`; Brucker and Knust record
`OMPT2||L_max` as minimal NP-hard in the strong sense with that attribution. NP membership: in a
yes-instance every start time of a job `j` is at most `d_j + y⁺`, so start times are a
certificate of polynomial size in the binary input, checked in polynomial time. With integer
data, integer start times lose no generality. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the stage processor sets are well formed for two processors
(`StagesWellFormed`), there is at least one job, every job lists one processing time per stage,
and there is one due date per job. -/
def WellFormed (i : MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) : Prop :=
  StagesWellFormed 2 i.1 ∧ i.2.1 ≠ [] ∧ (∀ job ∈ i.2.1, job.length = i.1.length) ∧
    i.2.2.1.length = i.2.1.length

/-- Some MPT open-shop schedule of the jobs completes every job `j` with lateness
`C_j - d_j ≤ y⁺ - y⁻`. -/
def MultiprocessorTaskOpenShopTwoMachinesMaximumLatenessFeasible
    (i : MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, IsMPTOpenShopSchedule i.1 (processingTime i) σ ∧
    ∀ j, completionTime (processingTime i) σ j + i.2.2.2.2 ≤ i.2.2.1.getD j 0 + i.2.2.2.1

open Classical in
/-- `OMPT2||L_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopTwoMachinesMaximumLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeOpenShopTwoMachinesMaximumLatenessInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultiprocessorTaskOpenShopTwoMachinesMaximumLatenessFeasible i)
  | none => false

/-- **`OMPT2||L_max` is NP-complete.** Source: Brucker and Knust, *Complexity results for
scheduling problems*; Lawler, Lenstra, and Rinnooy Kan (1981, 1982); Brucker (2007),
Chapter 11. -/
public theorem_wanted multiprocessorTaskOpenShopTwoMachinesMaximumLateness_npComplete :
    multiprocessorTaskOpenShopTwoMachinesMaximumLatenessDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopTwoMachinesMaximumLatenessDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesMaximumLateness
