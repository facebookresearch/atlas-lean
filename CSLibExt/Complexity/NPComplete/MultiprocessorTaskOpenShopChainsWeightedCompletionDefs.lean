/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MPT OPEN SHOP, CHAINS, UNIT TIMES, WEIGHTED COMPLETION TIME (OMPT2|chains; p_ij =
1|Σw_iC_i): definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT2|chains; p_ij = 1|Σw_iC_i` as minimal NP-hard in the strong sense
with the attribution to Timkovsky (2003);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (the MPT open-shop
model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsWeightedCompletion

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopPrecedenceSchedule)
open MultiprocessorTaskOpenShopChainsTardiness (MultiprocessorTaskOpenShopChainsTardinessInstance)

/-- Well-formedness of an instance: a well-formed `OMPT2|chains; p_ij = 1|ΣT_i` instance
(`MultiprocessorTaskOpenShopChainsTardiness.WellFormed`: two machines, well-formed stages, unit
processing times, chains) with at least one job. -/
def WellFormed (i : MultiprocessorTaskOpenShopChainsTardinessInstance) : Prop :=
  MultiprocessorTaskOpenShopChainsTardiness.WellFormed i ∧ 0 < i.2.2.1.length

/-- The weight `w_j` of job `j`: the number listed after its processing times. -/
def weight (i : MultiprocessorTaskOpenShopChainsTardinessInstance) (j : Fin i.2.2.1.length) : ℕ :=
  (i.2.2.1.get j).2

/-- Some unit-time MPT open-shop schedule obeys the chains and has total weighted completion time
`Σ_j w_j C_j ≤ K`. -/
def MultiprocessorTaskOpenShopChainsWeightedCompletionFeasible
    (i : MultiprocessorTaskOpenShopChainsTardinessInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTOpenShopPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧
      ∑ j, weight i j * completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `OMPT2|chains; p_ij = 1|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskOpenShopChainsTardinessInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultiprocessorTaskOpenShopChainsWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsWeightedCompletion
