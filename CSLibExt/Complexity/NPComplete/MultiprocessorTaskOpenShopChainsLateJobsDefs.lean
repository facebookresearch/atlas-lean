/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MPT OPEN SHOP, CHAINS, UNIT TIMES, LATE JOBS (OMPT2|chains; p_ij = 1|ΣU_i):
definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT2|chains; p_ij = 1|ΣU_i` as minimal NP-hard in the strong sense with
the attribution to Timkovsky (2003);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (the MPT open-shop
model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsLateJobs

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopPrecedenceSchedule)
open MultiprocessorTaskOpenShopChainsTardiness (MultiprocessorTaskOpenShopChainsTardinessInstance
  dueDate)

/-- Well-formedness of an instance: a well-formed `OMPT2|chains; p_ij = 1|ΣT_i` instance
(`MultiprocessorTaskOpenShopChainsTardiness.WellFormed`: two machines, well-formed stages, unit
processing times, chains) with at least one job. -/
def WellFormed (i : MultiprocessorTaskOpenShopChainsTardinessInstance) : Prop :=
  MultiprocessorTaskOpenShopChainsTardiness.WellFormed i ∧ 0 < i.2.2.1.length

/-- Some unit-time MPT open-shop schedule obeys the chains and has at most `K` late jobs
(`d_j < C_j`). -/
def MultiprocessorTaskOpenShopChainsLateJobsFeasible
    (i : MultiprocessorTaskOpenShopChainsTardinessInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTOpenShopPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧
      (Finset.univ.filter fun j => dueDate i j < completionTime (fun _ _ => 1) σ j).card ≤
        i.2.2.2.2

open Classical in
/-- `OMPT2|chains; p_ij = 1|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskOpenShopChainsTardinessInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultiprocessorTaskOpenShopChainsLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsLateJobs
