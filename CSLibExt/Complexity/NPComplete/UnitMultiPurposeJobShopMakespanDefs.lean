/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM3|p_ij=1|Cmax: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 242, problem [SS18] JOB-SHOP
SCHEDULING, comment (equal task lengths, `m = 3`);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Computational complexity of discrete optimization
problems", Annals of Discrete Mathematics 4 (1979), 121-140,
doi:10.1016/S0167-5060(08)70821-5;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `mpm_shop` (shop problems with multi-purpose machines), Universität Osnabrück.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultiPurposeJobShopMakespan

/-- An instance: the number `m` of machines; the jobs, job `j` being the list of its operations
in order, each operation given by the list of its eligible machines (numbered `1, …, m`); and
the bound `K`. -/
abbrev UnitMultiPurposeJobShopInstance := ℕ × List (List (List ℕ)) × ℕ

/-- An operation `O_{jk}` of the instance: a job `j` and a position `k < n_j`. -/
abbrev Operation (i : UnitMultiPurposeJobShopInstance) : Type :=
  (j : Fin i.2.1.length) × Fin (i.2.1.get j).length

/-- The eligible machines `μ_{jk}` of an operation. -/
def eligible (i : UnitMultiPurposeJobShopInstance) (t : Operation i) : List ℕ :=
  (i.2.1.get t.1).get t.2

/-- A schedule of the unit-time multi-purpose job shop: machine `μ t` and start time `σ t` for
every operation `t`, with every operation on an eligible machine, operations on the same
machine at different start times, and every operation of a job starting after the previous
operation of the job completes. -/
def IsUnitMPMSchedule (i : UnitMultiPurposeJobShopInstance) (μ σ : Operation i → ℕ) : Prop :=
  (∀ t, μ t ∈ eligible i t) ∧
    (∀ t t', μ t = μ t' → σ t = σ t' → t = t') ∧
    ∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 → σ ⟨j, k⟩ + 1 ≤ σ ⟨j, k'⟩

/-- An instance describes a multi-purpose job shop: every job has at least one operation, every
operation has a nonempty set of eligible machines, and every eligible machine lies in
`{1, …, m}`. -/
def IsMPMInstance (i : UnitMultiPurposeJobShopInstance) : Prop :=
  (∀ job ∈ i.2.1, job ≠ []) ∧ (∀ job ∈ i.2.1, ∀ μ ∈ job, μ ≠ []) ∧
    ∀ job ∈ i.2.1, ∀ μ ∈ job, ∀ M ∈ μ, 1 ≤ M ∧ M ≤ i.1

/-- Well-formedness of an instance: `m = 3`, and the instance describes a multi-purpose job
shop (`IsMPMInstance`). -/
def WellFormed (i : UnitMultiPurposeJobShopInstance) : Prop :=
  i.1 = 3 ∧ IsMPMInstance i

/-- Some schedule completes every operation by `K`: the last operation of every job, which
completes after the job's other operations, ends by `K`. -/
def UnitMultiPurposeJobShopMakespanFeasible (i : UnitMultiPurposeJobShopInstance) : Prop :=
  ∃ μ σ : Operation i → ℕ, IsUnitMPMSchedule i μ σ ∧
    ∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length → σ ⟨j, k⟩ + 1 ≤ i.2.2

open Classical in
/-- MULTIPURPOSE-MACHINE JOB SHOP `JMPM3|p_ij=1|C_max` as a decision problem over bitstrings. -/
noncomputable def unitMultiPurposeJobShopMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitMultiPurposeJobShopInstance) x with
  | some i => decide (WellFormed i ∧ UnitMultiPurposeJobShopMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitMultiPurposeJobShopMakespan
