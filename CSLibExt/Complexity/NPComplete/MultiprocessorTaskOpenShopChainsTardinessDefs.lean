/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MPT OPEN SHOP, CHAINS, UNIT TIMES, TOTAL TARDINESS (OMPT2|chains; p_ij = 1|ΣT_i):
definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT2|chains; p_ij = 1|∑ T_i` as minimal NP-hard in the strong sense with
the attribution to Timkovsky (2003);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (the MPT open-shop
model) and Section 1.3 (precedence relations).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsTardiness

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open UnitFlowShopPrecedenceMakespan (UnitJobs)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopPrecedenceSchedule)
open F3UnitChainsLateJobs (ChainsWellFormed)

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, the jobs
(job `i` listed by its processing times `(p_i1, …, p_ir)` and its due date `d_i`), the chain
arcs `(i, k)`, and the bound `K`. -/
abbrev MultiprocessorTaskOpenShopChainsTardinessInstance :=
  ℕ × List (List ℕ) × List (List ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The due date `d_i` of job `i`. -/
def dueDate (i : MultiprocessorTaskOpenShopChainsTardinessInstance)
    (j : Fin i.2.2.1.length) : ℕ :=
  (i.2.2.1.get j).2

/-- Well-formedness of an instance: two machines, a well-formed machine environment
(`StagesWellFormed`), `r` unit processing times per job (`UnitJobs`), and chain arcs
(`ChainsWellFormed`). -/
def WellFormed (i : MultiprocessorTaskOpenShopChainsTardinessInstance) : Prop :=
  i.1 = 2 ∧ StagesWellFormed i.1 i.2.1 ∧ UnitJobs i.2.1.length (i.2.2.1.map Prod.fst) ∧
    ChainsWellFormed i.2.2.1.length i.2.2.2.1

/-- Some MPT open-shop schedule of the unit-time jobs obeys the chains and has total tardiness
`∑_j (C_j - d_j)` (truncated subtraction) at most `K`. -/
def MultiprocessorTaskOpenShopChainsTardinessFeasible
    (i : MultiprocessorTaskOpenShopChainsTardinessInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTOpenShopPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧
      ∑ j, (completionTime (fun _ _ => 1) σ j - dueDate i j) ≤ i.2.2.2.2

open Classical in
/-- `OMPT2|chains; p_ij = 1|∑ T_i` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopChainsTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskOpenShopChainsTardinessInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopChainsTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsTardiness
