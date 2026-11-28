/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP O|p_ij=1;prec;no-wait|Cmax: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Open-shop problems with no-wait", minimal NP-hard entry
`O | p_ij = 1; prec; no-wait | C_max`, NP-hard in the strong sense, credited to Ullman (1975));
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopNoWaitPrecedenceMakespan

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan
  (UnitFlowShopPrecedenceMakespanInstance WellFormed)
open MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-- Some no-wait open-shop schedule completes every operation by time `K`: each job's operations
fill `m` consecutive unit slots, and the makespan `max_j C_j` is at most `K`. -/
def UnitOpenShopNoWaitPrecedenceMakespanFeasible (i : UnitFlowShopPrecedenceMakespanInstance) :
    Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsUnitOpenShopSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    (∀ j, ∃ s, ∀ k, s ≤ σ k j ∧ σ k j < s + i.1) ∧ ∀ k j, σ k j + 1 ≤ i.2.2.2

open Classical in
/-- NO-WAIT OPEN SHOP O|p_ij=1;prec;no-wait|Cmax as a decision problem over bitstrings. -/
noncomputable def unitOpenShopNoWaitPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopNoWaitPrecedenceMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopNoWaitPrecedenceMakespan
