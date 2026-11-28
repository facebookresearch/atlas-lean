/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O|p_ij=1;outtree|Lmax: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `o_nop` (open shop problems without
preemption), entry `O|p_ij=1;outtree|L_max` (minimal NP-hard in the strong sense, citing
Timkovsky 2003);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (not available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLateness
  (UnitFlowShopOutTreeMaxLatenessInstance WellFormed toInt)
open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan (Prec)

/-- `σ k j` (start of job `j`'s unit operation on machine `k`) is an open-shop schedule for the
precedence arcs `A`: each machine starts its operations at pairwise different times, each job
starts its operations at pairwise different times, and if job `i` precedes job `j` then every
operation of `j` starts after every operation of `i` is completed. -/
def IsUnitOpenShopSchedule (m n : ℕ) (A : List (ℕ × ℕ)) (σ : Fin m → Fin n → ℕ) : Prop :=
  (∀ k, Function.Injective (σ k)) ∧ (∀ j, Function.Injective fun k => σ k j) ∧
    ∀ i j, Prec A i j → ∀ k k', σ k i + 1 ≤ σ k' j

/-- Some open-shop schedule completes every operation of every job `j` by time `d_j + K`
(maximum lateness `max_j (C_j - d_j) ≤ K`). -/
def UnitOpenShopOutTreeMaxLatenessFeasible (i : UnitFlowShopOutTreeMaxLatenessInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsUnitOpenShopSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    ∀ (k : Fin i.1) (j : Fin i.2.1.length),
      ((σ k j + 1 : ℕ) : ℤ) - toInt (i.2.1.getD j ([], (0, 0))).2 ≤ toInt i.2.2.2

open Classical in
/-- OPEN SHOP O|p_ij=1;outtree|Lmax as a decision problem over bitstrings. -/
noncomputable def unitOpenShopOutTreeMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopOutTreeMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopOutTreeMaxLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness
