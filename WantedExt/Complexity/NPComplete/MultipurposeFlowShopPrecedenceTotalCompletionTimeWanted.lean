/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM FLOW SHOP, PRECEDENCE, TOTAL COMPLETION TIME (FMPM|prec; p_ij = 1|ΣC_i) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007): Section 1.3 (precedence
relations), Chapter 10 (the MPM flow-shop model) and Table 5.3 (`P|p_i = 1; prec|ΣC_i` is
NP-hard, Lenstra and Rinnooy Kan);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `FMPM|prec; p_ij = 1|ΣC_i` as strongly NP-hard with the attribution to
Lenstra and Rinnooy Kan (1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceTotalCompletionTime

open MultipurposeFlowShopPrecedenceMakespan (MultipurposeFlowShopPrecedenceMakespanInstance Job
  Stage WellFormed IsPrecedenceSchedule completionTime)

/-!
# MPM FLOW SHOP, PRECEDENCE, TOTAL COMPLETION TIME (FMPM|prec; p_ij = 1|ΣC_i) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM flow shop with `r ≥ 1` stages and machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij = 1`; a precedence relation `→` on the
jobs given by an acyclic digraph; and a bound `K`. QUESTION: is there a feasible schedule with
total completion time `Σ_i C_i ≤ K`?

The instance, its well-formedness and the schedules are those of `FMPM|prec; p_ij = 1|C_max`
(`WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted`, which states
Brucker's MPM flow-shop model and precedence relations): the instance type
`MultipurposeFlowShopPrecedenceMakespanInstance` (its last component read as the bound on
`Σ_i C_i`), `WellFormed`, `IsPrecedenceSchedule` and `completionTime` are reused unchanged; only
the objective differs. Binary encoding of all numbers (the problem is NP-complete in the strong
sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some MPM flow-shop schedule of the unit-time jobs obeys the precedence constraints and has
total completion time `Σ_i C_i` at most `K` (the instance's last component). -/
def MultipurposeFlowShopPrecedenceTotalCompletionTimeFeasible
    (i : MultipurposeFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsPrecedenceSchedule i.1 i.2.1 i.2.2.2.1 σ a ∧
      ∑ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `FMPM|prec; p_ij = 1|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def multipurposeFlowShopPrecedenceTotalCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeFlowShopPrecedenceTotalCompletionTimeFeasible i)
  | none => false

/-- **`FMPM|prec; p_ij = 1|ΣC_i` is NP-complete.** Source: Brucker (2007), Chapter 10 and
Table 5.3; Lenstra and Rinnooy Kan (1978); Brucker and Knust, *Complexity results for scheduling
problems*. -/
public theorem_wanted multipurposeFlowShopPrecedenceTotalCompletionTime_npComplete :
    multipurposeFlowShopPrecedenceTotalCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeFlowShopPrecedenceTotalCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceTotalCompletionTime
