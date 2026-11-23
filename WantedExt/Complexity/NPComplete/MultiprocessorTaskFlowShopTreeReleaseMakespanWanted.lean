/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP, TREE PRECEDENCE, RELEASE DATES (FMPT|tree; r_i; p_ij = 1|C_max) is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open UnitFlowShopPrecedenceMakespan (PrecWellFormed UnitJobs)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTPrecedenceSchedule)
open MultiprocessorTaskFlowShopTreeLateness (IsTreePrecedence)

/-!
# MPT FLOW SHOP, TREE PRECEDENCE, RELEASE DATES (FMPT|tree; r_i; p_ij = 1|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; a flow shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and machine sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `1, …, n`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij`
requires every machine of `μ_j` during its processing and `O_i,j+1` cannot start before `O_ij`
is completed; a release date `r_i ∈ ℤ₀⁺` for each job `i`, before which no operation of `i`
starts; a precedence relation `→` on the jobs that is a tree (an intree or an outtree); and a
bound `K`. Operations requiring a common machine cannot be processed simultaneously. QUESTION:
is there a feasible schedule with makespan `max_i C_i ≤ K`, where `C_i` is the completion time
of job `i` (that of its last operation)?

The MPT flow shop, its stage machine sets, unit-time schedules and job precedence are those of
`MultiprocessorTaskFlowShopPrecedenceMakespanWanted` (`FMPT|prec; p_ij = 1|C_max`), and the tree
condition `IsTreePrecedence` (an intree or an outtree, checked on the immediate predecessors of
the precedence relation, so forests are included and arcs implied by transitivity may be listed
or omitted) is that of `MultiprocessorTaskFlowShopTreeLatenessWanted`
(`FMPT|tree; p_ij = 1|L_max`); all are reused here. The release dates bound the start of every
operation of the job (equivalently of its first operation, by the stage order). Binary encoding
of all numbers.

Brucker and Knust's flow-shop table lists `F|p_ij = 1; intree; r_i|C_max` as strongly NP-hard
(Brucker and Knust 1999); it is the special case `r = m`, `μ_j = {M_j}` with an intree of this
problem.

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
(job `i` listed by its processing times `(p_i1, …, p_ir)` and its release date `r_i`), the arcs
`(i, k)` with `i → k`, and the bound `K`. -/
abbrev MultiprocessorTaskFlowShopTreeReleaseMakespanInstance :=
  ℕ × List (List ℕ) × List (List ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The release date `r_j` of job `j`. -/
def releaseDate (i : MultiprocessorTaskFlowShopTreeReleaseMakespanInstance)
    (j : Fin i.2.2.1.length) : ℕ :=
  (i.2.2.1.get j).2

/-- Well-formedness of an instance: the machine environment is well formed
(`StagesWellFormed`), every job has `r` unit processing times (`UnitJobs`), the listed arcs
describe an acyclic precedence digraph on the jobs (`PrecWellFormed`), and its
precedence relation is a tree (`IsTreePrecedence`). -/
def WellFormed (i : MultiprocessorTaskFlowShopTreeReleaseMakespanInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ UnitJobs i.2.1.length (i.2.2.1.map Prod.fst) ∧
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

/-- **`FMPT|tree; r_i; p_ij = 1|C_max` is NP-complete.** Source: Brucker and Knust (1999);
Brucker and Knust, *Complexity results for scheduling problems*; Brucker (2004), Chapter 11. -/
public theorem_wanted multiprocessorTaskFlowShopTreeReleaseMakespan_npComplete :
    multiprocessorTaskFlowShopTreeReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskFlowShopTreeReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopTreeReleaseMakespan
