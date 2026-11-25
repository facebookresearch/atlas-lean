/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP WITH PRECEDENCE AND UNIT TIMES (OMPM|prec; p_ij = 1|C_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5:
Chapter 10 (the MPM flow-shop and open-shop models), Section 1.3 (precedence relations) and
Table 5.3 (`P|p_i = 1; prec|C_max` is NP-hard in the strong sense, Ullman);
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `OMPM|prec; p_ij = 1|C_max` as minimal NP-hard in the strong sense, citing
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespan

open MultipurposeFlowShopPrecedenceMakespan (MultipurposeFlowShopPrecedenceMakespanInstance
  WellFormed Job Stage Prec completionTime)

/-!
# MPM OPEN SHOP WITH PRECEDENCE AND UNIT TIMES (OMPM|prec; p_ij = 1|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM open shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij` is processed by one
machine of `μ_j`, and the operations of a job are processed in any order but no two of them at
the same time; a precedence relation `→` on the jobs; and a bound `K`. Each machine processes at
most one operation at a time. QUESTION: is there a feasible schedule with makespan
`max_i C_i ≤ K`, where `C_i` is the completion time of job `i` (that of its last operation)?

The MPM open shop is Brucker's (*Scheduling Algorithms*, Chapter 10): "For the MPM flow shop
problem, each job `J_i` has exactly `r` operations `O_ij` (`j = 1, …, r`) and there is the same
machine set `μ_j` associated with the `j`-th operation of each job. [...] all machine sets are
assumed to be different [...]. MPM open shop problems are defined like MPM flow shop problems.
However, there are no precedence constraints between the operations of an MPM open shop", and,
as in every open shop, no two operations of a job are processed at the same time. Precedence
(Section 1.3): `i → k` means that `J_i` must be completed before `J_k` starts. Brucker and Knust
list the problem as minimal NP-hard in the strong sense. It contains `P|p_i = 1; prec|C_max`
(Brucker, Table 5.3: NP-hard in the strong sense, Ullman 1975) as the case of one stage whose
machine set holds all `m` machines, and the classical open shop `O|p_ij = 1; prec|C_max` as the
case `r = m`, `μ_j = {M_j}`. Membership in NP: the machines and start times are a certificate.

The instance, its well-formedness and the precedence relation are those of the MPM flow-shop
module `MultipurposeFlowShopPrecedenceMakespanWanted` (`FMPM|prec; p_ij = 1|C_max`), whose data
are the same: `MultipurposeFlowShopPrecedenceMakespanInstance` (the number `m` of machines, the
stage machine sets `[μ_1, …, μ_r]`, one list `[p_i1, …, p_ir]` of processing times per job, the
pairs `(i, k)` with `i → k`, and the bound `K`), `WellFormed` (at least one stage, machine
indices below `m`, pairwise different nonempty sets, every job with `r` unit processing times,
the pairs a strict partial order on the jobs), `Prec` (`i → k` when the pair `(i, k)` is listed)
and `completionTime` (the latest completion of a job's operations). Operation `(i, s)` gets a
start time `σ i s` and a machine `a i s ∈ μ_s`, and occupies the half-open interval
`[σ i s, σ i s + p_is)`. `IsMPMOpenShopSchedule` takes arbitrary processing times and
`IsMPMOpenShopPrecedenceSchedule` takes the instance data as arguments, so that the other MPM
open-shop problems of Brucker and Knust's class can state their questions with them. With
integer data, integer start times lose no generality. Binary encoding of all numbers (the
problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `σ` (start times) and `a` (machines) form an MPM open-shop schedule of `n` jobs with
processing times `p i s` on `m` machines with stage machine sets `μ`: each operation `(i, s)`
runs on a machine of `μ_s`; two different operations of the same job occupy disjoint time
intervals `[σ i s, σ i s + p i s)`; and two different operations on the same machine occupy
disjoint time intervals. -/
def IsMPMOpenShopSchedule {n : ℕ} (m : ℕ) (μ : List (List ℕ)) (p : Fin n → Fin μ.length → ℕ)
    (σ : Fin n → Fin μ.length → ℕ) (a : Fin n → Fin μ.length → Fin m) : Prop :=
  (∀ i s, (a i s : ℕ) ∈ μ.get s) ∧
    (∀ i s s', s ≠ s' →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i s') (σ i s' + p i s'))) ∧
    ∀ i s i' s', (i, s) ≠ (i', s') → a i s = a i' s' →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i' s') (σ i' s' + p i' s'))

/-- `σ` and `a` form an MPM open-shop schedule of `n` unit-time jobs (`p_ij = 1`) on `m`
machines with stage machine sets `μ` that obeys the precedence constraints of the listed pairs:
if `i → k`, then no operation of `k` starts before `C_i`. -/
def IsMPMOpenShopPrecedenceSchedule {n : ℕ} (m : ℕ) (μ : List (List ℕ)) (prs : List (ℕ × ℕ))
    (σ : Fin n → Fin μ.length → ℕ) (a : Fin n → Fin μ.length → Fin m) : Prop :=
  IsMPMOpenShopSchedule m μ (fun _ _ => 1) σ a ∧
    ∀ i k, Prec prs i k → ∀ s, completionTime (fun _ _ => 1) σ i ≤ σ k s

/-- Some MPM open-shop schedule of the unit-time jobs obeys the precedence constraints and has
makespan at most `K`. -/
def MultipurposeOpenShopPrecedenceMakespanFeasible
    (i : MultipurposeFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsMPMOpenShopPrecedenceSchedule i.1 i.2.1 i.2.2.2.1 σ a ∧
      ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `OMPM|prec; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeOpenShopPrecedenceMakespanFeasible i)
  | none => false

/-- **`OMPM|prec; p_ij = 1|C_max` is NP-complete.** Source: Brucker (2007), Chapter 10 and
Table 5.3; Ullman (1975); Brucker and Knust, *Complexity results for scheduling problems*
(Timkovsky 2003). -/
public theorem_wanted multipurposeOpenShopPrecedenceMakespan_npComplete :
    multipurposeOpenShopPrecedenceMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeOpenShopPrecedenceMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespan
