/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP, PRECEDENCE, TOTAL COMPLETION TIME (OMPM|prec; p_ij = 1|ΣC_i): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceTotalCompletionTime

open MultipurposeFlowShopPrecedenceMakespan (MultipurposeFlowShopPrecedenceMakespanInstance
  WellFormed Job Stage completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)

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

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceTotalCompletionTime
