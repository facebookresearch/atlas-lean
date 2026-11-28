/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK JOB SHOP JMPT2|chains;p_ij=1|ΣC_i: definitions

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8
(`J2|chains, p_ij = 1|∑ C_j` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `mpt_shop` (shop problems with multiprocessor tasks), Universität Osnabrück, which lists
`JMPT2|chains; p_ij = 1|∑ C_i` as minimal NP-hard in the strong sense, citing Timkovsky (1998);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the multiprocessor-task model) and Section 1.3 (chains).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopChainsCompletionTime

open UnitMultiPurposeJobShopMakespan (UnitMultiPurposeJobShopInstance Operation)
open UnitMultiprocessorTaskJobShopMakespan (IsUnitMPTSchedule)

/-- An instance: a `JMPT2|p_ij = 1|C_max` instance (`m`, the jobs, and the bound `K`, here on the
total completion time) and the arcs `(j, j')` of the chains, `j` the immediate predecessor of
`j'`. -/
abbrev UnitMultiprocessorTaskJobShopChainsCompletionTimeInstance :=
  UnitMultiPurposeJobShopInstance × List (ℕ × ℕ)

/-- The arc relation of the chains: `j` is the immediate predecessor of `j'` when the pair
`(j, j')` is listed. -/
def Arc (i : UnitMultiprocessorTaskJobShopChainsCompletionTimeInstance)
    (j j' : Fin i.1.2.1.length) : Prop :=
  ((j : ℕ), (j' : ℕ)) ∈ i.2

/-- Well-formedness of an instance: a well-formed `JMPT2|p_ij = 1|C_max` instance (`m = 2`,
every job nonempty, every processor set nonempty in `{1, 2}`), every arc names two jobs, no two
distinct arcs share their tail (at most one immediate successor) or their head (at most one
immediate predecessor), and the arcs have no cycle. -/
def WellFormed (i : UnitMultiprocessorTaskJobShopChainsCompletionTimeInstance) : Prop :=
  UnitMultiprocessorTaskJobShopMakespan.WellFormed i.1 ∧
    (∀ a ∈ i.2, a.1 < i.1.2.1.length ∧ a.2 < i.1.2.1.length) ∧
    (∀ a ∈ i.2, ∀ b ∈ i.2, a.1 = b.1 → a = b) ∧
    (∀ a ∈ i.2, ∀ b ∈ i.2, a.2 = b.2 → a = b) ∧
    ∀ j, ¬ Relation.TransGen (Arc i) j j

/-- Some unit-time multiprocessor-task job-shop schedule meets the chains and has total
completion time at most `K`: the first task of a job starts no earlier than the last task of its
immediate predecessor completes, and the completion times `C j` (the completion times of the last
tasks) sum to at most `K`. -/
def UnitMultiprocessorTaskJobShopChainsCompletionTimeFeasible
    (i : UnitMultiprocessorTaskJobShopChainsCompletionTimeInstance) : Prop :=
  ∃ σ : Operation i.1 → ℕ, IsUnitMPTSchedule i.1 σ ∧
    (∀ j j', Arc i j j' → ∀ (k : Fin (i.1.2.1.get j).length)
      (k' : Fin (i.1.2.1.get j').length), k.1 + 1 = (i.1.2.1.get j).length → k'.1 = 0 →
        σ ⟨j, k⟩ + 1 ≤ σ ⟨j', k'⟩) ∧
    ∃ C : Fin i.1.2.1.length → ℕ,
      (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
        C j = σ ⟨j, k⟩ + 1) ∧
      ∑ j, C j ≤ i.1.2.2

open Classical in
/-- MULTIPROCESSOR-TASK JOB SHOP `JMPT2|chains;p_ij=1|ΣC_i` as a decision problem over
bitstrings. -/
noncomputable def unitMultiprocessorTaskJobShopChainsCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitMultiprocessorTaskJobShopChainsCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ UnitMultiprocessorTaskJobShopChainsCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopChainsCompletionTime
