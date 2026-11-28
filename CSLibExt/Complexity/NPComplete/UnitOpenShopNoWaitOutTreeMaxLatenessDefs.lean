/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Open-shop problems with no-wait", minimal NP-hard entry
`O | p_ij = 1; outtree; no-wait | L_max`, NP-hard in the strong sense, credited to Brucker, Garey
and Johnson (1977));
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2(3)
(1977), 275-284, doi:10.1287/moor.2.3.275.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLatenessDefs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopNoWaitOutTreeMaxLateness

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLateness
  (UnitFlowShopOutTreeMaxLatenessInstance WellFormed toInt)
open MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-- Some no-wait open-shop schedule completes every operation of every job `j` by time
`d_j + K`: each job's operations fill `m` consecutive unit slots, and the maximum lateness
`max_j (C_j - d_j)` is at most `K`. -/
def UnitOpenShopNoWaitOutTreeMaxLatenessFeasible (i : UnitFlowShopOutTreeMaxLatenessInstance) :
    Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsUnitOpenShopSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    (∀ j, ∃ s, ∀ k, s ≤ σ k j ∧ σ k j < s + i.1) ∧
    ∀ (k : Fin i.1) (j : Fin i.2.1.length),
      ((σ k j + 1 : ℕ) : ℤ) - toInt (i.2.1.getD j ([], (0, 0))).2 ≤ toInt i.2.2.2

open Classical in
/-- NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax as a decision problem over bitstrings. -/
noncomputable def unitOpenShopNoWaitOutTreeMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopOutTreeMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopNoWaitOutTreeMaxLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopNoWaitOutTreeMaxLateness
