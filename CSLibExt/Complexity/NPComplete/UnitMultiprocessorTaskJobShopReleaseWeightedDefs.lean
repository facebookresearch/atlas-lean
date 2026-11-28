/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK JOB SHOP JMPT2|r_i;p_ij=1|Σw_iC_i: definitions

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8
(the dedicated case `J2|r_j, p_ij = 1|∑ w_j C_j`, recorded by Brucker and Knust as strongly
NP-hard);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `mpt_shop` (shop problems with multiprocessor tasks), Universität Osnabrück, which lists
`JMPT2|r_i; p_ij = 1|∑ w_i C_i` as minimal NP-hard in the strong sense, citing Timkovsky (1998);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the multiprocessor-task model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopReleaseWeighted

open UnitMultiPurposeJobShopMakespan (UnitMultiPurposeJobShopInstance Operation)
open UnitMultiprocessorTaskJobShopMakespan (IsUnitMPTSchedule)

/-- An instance: a `JMPT2|p_ij = 1|C_max` instance (`m`, the jobs, and the bound `K`, here on the
total weighted completion time) and the pairs `(r_j, w_j)` of release dates and weights, one per
job. -/
abbrev UnitMultiprocessorTaskJobShopReleaseWeightedInstance :=
  UnitMultiPurposeJobShopInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed `JMPT2|p_ij = 1|C_max` instance (`m = 2`,
every job nonempty, every processor set nonempty in `{1, 2}`), and one pair `(r_j, w_j)` per
job. -/
def WellFormed (i : UnitMultiprocessorTaskJobShopReleaseWeightedInstance) : Prop :=
  UnitMultiprocessorTaskJobShopMakespan.WellFormed i.1 ∧ i.2.length = i.1.2.1.length

/-- Some unit-time multiprocessor-task job-shop schedule starts the first task of every job no
earlier than its release date `r_j` and has `∑_j w_j C_j ≤ K`, where `C j` is the completion
time of the last task of job `j`. -/
def UnitMultiprocessorTaskJobShopReleaseWeightedFeasible
    (i : UnitMultiprocessorTaskJobShopReleaseWeightedInstance) : Prop :=
  ∃ σ : Operation i.1 → ℕ, IsUnitMPTSchedule i.1 σ ∧
    (∀ j (k : Fin (i.1.2.1.get j).length), k.1 = 0 → (i.2.getD j (0, 0)).1 ≤ σ ⟨j, k⟩) ∧
    ∃ C : Fin i.1.2.1.length → ℕ,
      (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
        C j = σ ⟨j, k⟩ + 1) ∧
      ∑ j : Fin i.1.2.1.length, (i.2.getD j (0, 0)).2 * C j ≤ i.1.2.2

open Classical in
/-- MULTIPROCESSOR-TASK JOB SHOP `JMPT2|r_i;p_ij=1|Σw_iC_i` as a decision problem over
bitstrings. -/
noncomputable def unitMultiprocessorTaskJobShopReleaseWeightedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitMultiprocessorTaskJobShopReleaseWeightedInstance) x with
  | some i => decide (WellFormed i ∧ UnitMultiprocessorTaskJobShopReleaseWeightedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopReleaseWeighted
