/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP O|p_ij=1;prec;no-wait|ΣC_i: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Open-shop problems with no-wait", minimal NP-hard entry
`O | p_ij = 1; prec; no-wait | Σ C_i`, NP-hard in the strong sense, credited to Lenstra and
Rinnooy Kan (1978));
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence constraints",
Operations Research 26(1) (1978), 22-35, doi:10.1287/opre.26.1.22.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopNoWaitPrecedenceTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan
  (UnitFlowShopPrecedenceMakespanInstance WellFormed)
open MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-- Some no-wait open-shop schedule has total completion time at most `K`: each job's
operations fill `m` consecutive unit slots, and `Σ_j max_k (σ k j + 1) ≤ K`. -/
def UnitOpenShopNoWaitPrecedenceTotalCompletionFeasible
    (i : UnitFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsUnitOpenShopSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    (∀ j, ∃ s, ∀ k, s ≤ σ k j ∧ σ k j < s + i.1) ∧
    ∑ j, Finset.univ.sup (fun k => σ k j + 1) ≤ i.2.2.2

open Classical in
/-- NO-WAIT OPEN SHOP O|p_ij=1;prec;no-wait|ΣC_i as a decision problem over bitstrings. -/
noncomputable def unitOpenShopNoWaitPrecedenceTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopNoWaitPrecedenceTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopNoWaitPrecedenceTotalCompletion
