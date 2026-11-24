/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH TWO PROCESSORS, TOTAL COMPLETION TIME (OMPT2||ΣC_i) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (multiprocessor
tasks: the MPT open-shop model);
J. O. Achugbue and F. Y. Chin, "Scheduling the open shop to minimize mean flow time", SIAM
Journal on Computing 11(4) (1982), 709-720, doi:10.1137/0211058;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT2||ΣC_i` as minimal NP-hard in the strong sense with the attribution
to Achugbue and Chin (1982).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobsWanted
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesTotalCompletion

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance Job Stage
  processingTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopSchedule)

/-!
# MPT OPEN SHOP WITH TWO PROCESSORS, TOTAL COMPLETION TIME (OMPT2||ΣC_i) is NP-complete

INSTANCE: two processors `M_1, M_2`; an open shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and processor sets `μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `1, …, n` with
`n ≥ 1`, each consisting of `r` tasks `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`, where
`O_ij` requires every processor of `μ_j` during its processing; and a bound `K`. Tasks requiring a
common processor cannot be processed simultaneously, and no two tasks of the same job can be
processed simultaneously; the tasks of a job may be processed in any order. QUESTION: is there a
feasible schedule with total completion time `Σ_i C_i ≤ K`, where `C_i` is the completion time of
job `i` (that of its last task)?

The MPT model is Brucker's (*Scheduling Algorithms*, 5th ed., Chapter 11): every job consists of
`r` tasks, the processor set depends only on the stage, `μ_ij = μ_j`, with pairwise different
`μ_j`, and "open shop problems with MPT are defined as flow shop problems with MPT but without
precedence constraints between tasks. However, no pair of tasks of the same job can be processed
simultaneously." In `OMPT2`, the number of processors is fixed to `2`. The MPT open-shop schedule
`IsMPTOpenShopSchedule` (task `(i, s)` gets a start time `σ i s` and occupies the half-open
interval `[σ i s, σ i s + p_is)` on every processor of `μ_s`; two different tasks of the same
job, or two different tasks whose processor sets share a processor, occupy disjoint intervals) is
that of `OMPT|prec; p_ij = 1|C_max` (`MultiprocessorTaskOpenShopPrecedenceMakespanWanted`),
which takes arbitrary processing times; a task with `p_is = 0` occupies no time. The instance
shape and its accessors (`Job`, `Stage`, `processingTime`: the number of processors `m`, the stage
processor sets, one list of `r` processing times per job, and `K`) are those of `FMPM|n = 3|C_max`
(`MultipurposeFlowShopThreeJobsWanted`); here `m = 2` and the number of jobs is arbitrary.
`StagesWellFormed` (at least one stage, processor indices below `m`, pairwise different sets
compared as `Finset`s) and `completionTime` (the latest completion of a job's tasks) are those of
`MultipurposeFlowShopPrecedenceMakespanWanted`. The classical two-processor open shop
`O2||ΣC_i`, which Achugbue and Chin (1982) prove NP-complete even when the input length is
measured by the sum of the task lengths, is the case `r = 2`, `μ_j = {M_j}`, so `OMPT2||ΣC_i` is
NP-hard in the strong sense; Brucker and Knust record it as a minimal NP-hard problem of the MPT
shop class. NP membership: a schedule is given by start times, each at most `K` in a
yes-instance, so it is a certificate of polynomial size in the binary input, checked in
polynomial time. With integer data, integer start times lose no generality. Binary encoding of
all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: there are two processors (`m = 2`), the stage processor sets
are well formed (`StagesWellFormed`), every job lists one processing time per stage, and there is
at least one job (as in `TwoProcessorOpenShopMeanFlowTimeWanted`). -/
def WellFormed (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  i.1 = 2 ∧ StagesWellFormed i.1 i.2.1 ∧ (∀ job ∈ i.2.2.1, job.length = i.2.1.length) ∧
    0 < i.2.2.1.length

/-- Some MPT open-shop schedule of the jobs has total completion time at most `K`. -/
def MultiprocessorTaskOpenShopTwoMachinesTotalCompletionFeasible
    (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, IsMPTOpenShopSchedule i.2.1 (processingTime i) σ ∧
    ∑ j, completionTime (processingTime i) σ j ≤ i.2.2.2

open Classical in
/-- `OMPT2||ΣC_i` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopTwoMachinesTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopThreeJobsInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultiprocessorTaskOpenShopTwoMachinesTotalCompletionFeasible i)
  | none => false

/-- **`OMPT2||ΣC_i` is NP-complete.** Source: Brucker (2007), Chapter 11; Achugbue and Chin
(1982); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted multiprocessorTaskOpenShopTwoMachinesTotalCompletion_npComplete :
    multiprocessorTaskOpenShopTwoMachinesTotalCompletionDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopTwoMachinesTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesTotalCompletion
