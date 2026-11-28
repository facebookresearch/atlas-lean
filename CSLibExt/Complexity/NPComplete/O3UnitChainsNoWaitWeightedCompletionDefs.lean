/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|Σw_iC_i`: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `o_now` (open-shop problems with
no-wait), entry `O3|p_ij=1;chains;no-wait|Σw_iC_i` (minimal NP-hard in the strong sense, citing
Timkovsky 2003);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (only the abstract and introduction were available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.F3UnitChainsWeightedCompletionDefs
public import CSLibExt.Complexity.NPComplete.O3UnitChainsNoWaitLateJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.O3UnitChainsNoWaitWeightedCompletion

open F3UnitChainsWeightedCompletion (F3UnitChainsWeightedCompletionInstance WellFormed)
open O3UnitChainsNoWaitLateJobs (IsNoWaitSchedule)

/-- Some no-wait schedule has total weighted completion time at most `K`, with
`C_j = S j + 3`. -/
def O3UnitChainsNoWaitWeightedCompletionFeasible (i : F3UnitChainsWeightedCompletionInstance) :
    Prop :=
  ∃ (S : Fin i.1.length → ℕ) (σ : Fin 3 → Fin i.1.length → ℕ),
    IsNoWaitSchedule 3 i.1.length i.2.1 S σ ∧ ∑ j, i.1.get j * (S j + 3) ≤ i.2.2

open Classical in
/-- `O3|p_ij=1;chains;no-wait|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def o3UnitChainsNoWaitWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ O3UnitChainsNoWaitWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.O3UnitChainsNoWaitWeightedCompletion
