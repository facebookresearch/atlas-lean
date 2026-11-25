/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP, PRECEDENCE, TOTAL COMPLETION TIME (OMPM|prec; p_ij = 1|ΣC_i) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5:
Chapter 10 (the MPM open-shop model), Section 1.3 (precedence relations) and Table 5.3
(`P|p_i = 1; prec|ΣC_i` is NP-hard in the strong sense, Lenstra and Rinnooy Kan);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `OMPM|prec; p_ij = 1|ΣC_i` as minimal NP-hard in the strong sense with the
attribution to Lenstra and Rinnooy Kan (1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceTotalCompletionTime

open MultipurposeFlowShopPrecedenceMakespan (MultipurposeFlowShopPrecedenceMakespanInstance
  WellFormed Job Stage completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)

/-!
# MPM OPEN SHOP, PRECEDENCE, TOTAL COMPLETION TIME (OMPM|prec; p_ij = 1|ΣC_i) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM open shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij` is processed by one
machine of `μ_j`, and the operations of a job are processed in any order but no two of them at
the same time; a precedence relation `→` on the jobs; and a bound `K`. Each machine processes at
most one operation at a time. QUESTION: is there a feasible schedule with total completion time
`Σ_i C_i ≤ K`, where `C_i` is the completion time of job `i` (that of its last operation)?

This is the MPM open shop with precedence constraints of
`MultipurposeOpenShopPrecedenceMakespanWanted` (`OMPM|prec; p_ij = 1|C_max`; Brucker, *Scheduling
Algorithms*, Chapter 10 and Section 1.3) with the total completion time in place of the
makespan. Brucker and Knust list it as minimal NP-hard in the strong sense, citing Lenstra and
Rinnooy Kan (1978). It contains `P|p_i = 1; prec|ΣC_i` (Brucker, Table 5.3: NP-hard in the strong
sense, Lenstra and Rinnooy Kan) as the case of one stage whose machine set holds all `m`
machines. Membership in NP: the machines and start times are a certificate.

The instance, its well-formedness and `completionTime` are those of the MPM flow-shop module
`MultipurposeFlowShopPrecedenceMakespanWanted`, and the schedules
(`IsMPMOpenShopPrecedenceSchedule`: machines from the stage sets, no two operations of a job or
of a machine at the same time, precedence constraints between jobs) those of
`MultipurposeOpenShopPrecedenceMakespanWanted`; the last component of the instance is the bound
`K` on `Σ_i C_i`. Binary encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some MPM open-shop schedule of the unit-time jobs obeys the precedence constraints and has
total completion time `Σ_i C_i` at most `K`. -/
def MultipurposeOpenShopPrecedenceTotalCompletionTimeFeasible
    (i : MultipurposeFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsMPMOpenShopPrecedenceSchedule i.1 i.2.1 i.2.2.2.1 σ a ∧
      ∑ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `OMPM|prec; p_ij = 1|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopPrecedenceTotalCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeOpenShopPrecedenceTotalCompletionTimeFeasible i)
  | none => false

/-- **`OMPM|prec; p_ij = 1|ΣC_i` is NP-complete.** Source: Brucker (2007), Chapter 10 and
Table 5.3; Lenstra and Rinnooy Kan (1978); Brucker and Knust, *Complexity results for scheduling
problems*. -/
public theorem_wanted multipurposeOpenShopPrecedenceTotalCompletionTime_npComplete :
    multipurposeOpenShopPrecedenceTotalCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeOpenShopPrecedenceTotalCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceTotalCompletionTime
