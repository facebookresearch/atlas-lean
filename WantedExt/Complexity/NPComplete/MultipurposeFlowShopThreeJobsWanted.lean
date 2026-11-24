/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM FLOW SHOP WITH THREE JOBS (FMPM|n = 3|C_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM flow-shop
model; Section 10.2: "Proceeding as for problem JMPM2|n = 3|C_max, FMPM|n = 3|C_max and
OMPM|n = 3|C_max can be shown to be NP-hard");
P. Brucker, B. Jurisch and A. Krämer, "Complexity of scheduling problems with multi-purpose
machines", Annals of Operations Research 70 (1997), 57-73, doi:10.1023/A:1018950911030;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `FMPM|n = 3|C_max` as NP-hard with the attribution to Brucker, Jurisch
and Krämer (1997).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobs

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed IsMPMFlowShopSchedule
  completionTime)

/-!
# MPM FLOW SHOP WITH THREE JOBS (FMPM|n = 3|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM flow shop with `r ≥ 1` stages and machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; exactly three jobs `J_1, J_2, J_3`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`; and a bound
`K`. QUESTION: is there a feasible schedule with makespan `max_i C_i ≤ K`?

The MPM flow-shop model and its schedules are those of `FMPM|prec; p_ij = 1|C_max`
(`WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted`, which states
Brucker's model with arbitrary processing times: `StagesWellFormed`, `IsMPMFlowShopSchedule`,
`completionTime`, reused here): operation `O_ij` runs on one machine of `μ_j`, `O_ij` cannot
start before `O_i,j-1` is completed, and no two time intervals `[S_ij, S_ij + p_ij)` overlap on
the same machine. There are no precedence constraints between jobs and no release dates. The
number of machines `m` and the number of stages `r` are part of the instance. Processing times
are listed per job, one list of `r` numbers each. Binary encoding of all numbers (the problem is
NP-hard in the ordinary sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, one list
`[p_i1, …, p_ir]` of processing times per job, and the bound `K`. -/
abbrev MultipurposeFlowShopThreeJobsInstance := ℕ × List (List ℕ) × List (List ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed jobs (`n = 3` in a well-formed instance). -/
abbrev Job (i : MultipurposeFlowShopThreeJobsInstance) : Type := Fin i.2.2.1.length

/-- The stages of the instance, `Fin r` for `r` machine sets. -/
abbrev Stage (i : MultipurposeFlowShopThreeJobsInstance) : Type := Fin i.2.1.length

/-- The processing time `p_js` of the operation of job `j` in stage `s`. -/
def processingTime (i : MultipurposeFlowShopThreeJobsInstance) (j : Job i) (s : Stage i) : ℕ :=
  (i.2.2.1.get j).getD s 0

/-- Well-formedness of an instance: the machine environment is well formed, there are exactly
three jobs, and every job lists one processing time per stage. -/
def WellFormed (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ i.2.2.1.length = 3 ∧ ∀ job ∈ i.2.2.1, job.length = i.2.1.length

/-- Some MPM flow-shop schedule of the jobs has makespan at most `K`. -/
def MultipurposeFlowShopThreeJobsFeasible (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsMPMFlowShopSchedule i.1 i.2.1 (processingTime i) σ a ∧
      ∀ j, completionTime (processingTime i) σ j ≤ i.2.2.2

open Classical in
/-- `FMPM|n = 3|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeFlowShopThreeJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopThreeJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeFlowShopThreeJobsFeasible i)
  | none => false

/-- **`FMPM|n = 3|C_max` is NP-complete.** Source: Brucker (2007), Chapter 10; Brucker, Jurisch
and Krämer (1997); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted multipurposeFlowShopThreeJobs_npComplete :
    multipurposeFlowShopThreeJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeFlowShopThreeJobsDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobs
