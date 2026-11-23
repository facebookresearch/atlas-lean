/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM2|chains|Cmax is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Shop problems with multipurpose machines" (`OMPM2|chains|C_max`, minimal NP-hard in the
strong sense, credited to V. S. Tanaev, Y. N. Sotskov, and V. A. Strusevich, *Scheduling Theory.
Multi-Stage Systems*, Kluwer (1994), doi:10.1007/978-94-011-1192-8, which was not available;
their two-machine open shop `O2|chains|C_max` is the case `μ_j = {M_j}`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.F3UnitChainsLateJobsWanted
public import WantedExt.Complexity.NPComplete.MultipurposeOpenShopMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesChainsMakespan

open F3UnitChainsLateJobs (ChainsWellFormed)
open MultipurposeFlowShopPrecedenceMakespan (Prec completionTime)
open MultipurposeFlowShopThreeJobs (Job Stage processingTime)
open MultipurposeOpenShopMakespan (MultipurposeOpenShopMakespanInstance)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-!
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM2|chains|Cmax is NP-complete

INSTANCE: two machines `M_1, M_2`; an MPM open shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`, where `O_ij` is processed by one
machine of `μ_j`, and the operations of a job are processed in any order but no two of them at
the same time; a precedence relation on the jobs consisting of disjoint chains (each job has at
most one immediate predecessor and at most one immediate successor), where `i → k` means that
no operation of `k` starts before `J_i` is completed; and a bound `K`. Each machine processes at
most one operation at a time. QUESTION: is there a feasible schedule with makespan
`max_i C_i ≤ K`, where `C_i` is the completion time of job `i` (that of its last operation)?

This is Brucker and Knust's `OMPM2|chains|C_max`, which they classify as NP-hard in the strong
sense, citing Tanaev, Sotskov, and Strusevich (1994) for the two-machine open shop
`O2|chains|C_max`, the case `r = 2`, `μ_1 = {M_1}`, `μ_2 = {M_2}`. It is `OMPM||C_max`
(`MultipurposeOpenShopMakespanWanted`) with `m = 2` and chain precedences: the instance pairs that
module's instance (`m`, the machine sets, one list of processing times per job, `K`) with the
chain arcs `(i, k)` (`J_i` the immediate predecessor of `J_k`), and `WellFormed` is that module's
well-formedness plus `m = 2` and `F3UnitChainsLateJobs.ChainsWellFormed` (distinct arcs naming
jobs, no job with two immediate successors or two immediate predecessors, no cycle). The schedule
is `IsMPMOpenShopSchedule` (`MultipurposeOpenShopPrecedenceMakespanWanted`) with the makespan
bound through `completionTime` (`MultipurposeFlowShopPrecedenceMakespanWanted`), plus, for every
arc `(i, k)` (`Prec` of the listed arcs), `C_i ≤ σ k s` for every operation of `k`, as in
`IsMPMOpenShopPrecedenceSchedule`; respecting every arc respects every pair of the generated
order. Binary encoding of all numbers. Membership in NP: the machines and start times (each at
most `K`) are a certificate checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: an `OMPM||C_max` instance (the number `m` of machines, the stage machine sets,
one list of processing times per job, the bound `K`) and the chain arcs `(i, k)`. -/
abbrev MultipurposeOpenShopTwoMachinesChainsMakespanInstance :=
  MultipurposeOpenShopMakespanInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed `OMPM||C_max` instance with `m = 2` machines,
whose arcs form chains on the jobs. -/
def WellFormed (i : MultipurposeOpenShopTwoMachinesChainsMakespanInstance) : Prop :=
  MultipurposeOpenShopMakespan.WellFormed i.1 ∧ i.1.1 = 2 ∧
    ChainsWellFormed i.1.2.2.1.length i.2

/-- Some MPM open-shop schedule of the jobs respects the chains (if `J_i` immediately precedes
`J_k`, no operation of `k` starts before `C_i`) and has makespan at most `K`. -/
def MultipurposeOpenShopTwoMachinesChainsMakespanFeasible
    (i : MultipurposeOpenShopTwoMachinesChainsMakespanInstance) : Prop :=
  ∃ σ : Job i.1 → Stage i.1 → ℕ, ∃ a : Job i.1 → Stage i.1 → Fin i.1.1,
    IsMPMOpenShopSchedule i.1.1 i.1.2.1 (processingTime i.1) σ a ∧
      (∀ j k, Prec i.2 j k → ∀ s, completionTime (processingTime i.1) σ j ≤ σ k s) ∧
      ∀ j, completionTime (processingTime i.1) σ j ≤ i.1.2.2.2

open Classical in
/-- `OMPM2|chains|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopTwoMachinesChainsMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeOpenShopTwoMachinesChainsMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeOpenShopTwoMachinesChainsMakespanFeasible i)
  | none => false

/-- **`OMPM2|chains|C_max` is NP-complete.** Source: Brucker and Knust's classification; Tanaev,
Sotskov, and Strusevich (1994). -/
public theorem_wanted multipurposeOpenShopTwoMachinesChainsMakespan_npComplete :
    multipurposeOpenShopTwoMachinesChainsMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeOpenShopTwoMachinesChainsMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesChainsMakespan
