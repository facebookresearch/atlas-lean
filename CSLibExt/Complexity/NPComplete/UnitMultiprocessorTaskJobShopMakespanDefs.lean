/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK JOB SHOP JMPT2|p_ij=1|Cmax: definitions

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the multiprocessor-task model) and Section 11.2, "Job Shop Problems" (records that
`JMPT2|p_ij = 1|C_max` is NP-hard, credited to Brucker and Krämer);
P. Brucker and A. Krämer, "Shop scheduling problems with multiprocessor tasks on dedicated
processors", Annals of Operations Research 57 (1995), 13-27, doi:10.1007/BF02099688 (not
available; Brucker's book records the result and its attribution);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `mpt_shop` (shop problems with multiprocessor tasks), Universität Osnabrück, which lists
`JMPT2|p_ij = 1|C_max` as minimal NP-hard in the strong sense, citing Brucker and Krämer (1995).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitMultiPurposeJobShopMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopMakespan

open UnitMultiPurposeJobShopMakespan (UnitMultiPurposeJobShopInstance Operation eligible
  IsMPMInstance)

/-- A schedule of the unit-time multiprocessor-task job shop: start times `σ` such that two
different tasks whose processor sets share a processor start at different times (with unit
processing times, they do not overlap), and every task of a job starts after the previous task
of the job completes. -/
def IsUnitMPTSchedule (i : UnitMultiPurposeJobShopInstance) (σ : Operation i → ℕ) : Prop :=
  (∀ t t', t ≠ t' → (∃ M, M ∈ eligible i t ∧ M ∈ eligible i t') → σ t ≠ σ t') ∧
    ∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 → σ ⟨j, k⟩ + 1 ≤ σ ⟨j, k'⟩

/-- Well-formedness of an instance: `m = 2`, and the instance describes a job shop whose tasks
have nonempty processor sets in `{1, …, m}` (`IsMPMInstance`). -/
def WellFormed (i : UnitMultiPurposeJobShopInstance) : Prop :=
  i.1 = 2 ∧ IsMPMInstance i

/-- Some schedule completes every task by `K`: the last task of every job, which completes after
the job's other tasks, ends by `K`. -/
def UnitMultiprocessorTaskJobShopMakespanFeasible (i : UnitMultiPurposeJobShopInstance) :
    Prop :=
  ∃ σ : Operation i → ℕ, IsUnitMPTSchedule i σ ∧
    ∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length → σ ⟨j, k⟩ + 1 ≤ i.2.2

open Classical in
/-- MULTIPROCESSOR-TASK JOB SHOP `JMPT2|p_ij=1|C_max` as a decision problem over bitstrings. -/
noncomputable def unitMultiprocessorTaskJobShopMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitMultiPurposeJobShopInstance) x with
  | some i => decide (WellFormed i ∧ UnitMultiprocessorTaskJobShopMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopMakespan
