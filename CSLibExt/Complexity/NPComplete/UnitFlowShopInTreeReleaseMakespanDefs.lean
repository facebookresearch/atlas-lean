/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP F|p_ij=1;intree;r_i|Cmax: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Flow-shop problems without preemption", minimal NP-hard entry
`F | p_ij = 1; intree; r_i | C_max`); P. Brucker and S. Knust, "Complexity results for
single-machine problems with positive finish-start time-lags", Computing 63 (1999), 299-316,
doi:10.1007/s006070050036.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopInTreeReleaseMakespan

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan
  (Prec PrecWellFormed IsSchedule UnitJobs)

/-- An instance `(m, J, A, K)`: the number of machines `m`, the jobs `J` (job `j` listed as its
processing times `(p_j1, …, p_jm)` and its release date `r_j`), the precedence arcs `A`
(`(i, j)`: job `i` precedes job `j`), and the bound `K`. -/
abbrev UnitFlowShopInTreeReleaseMakespanInstance := ℕ × List (List ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance `(m, J, A, K)`: `m ≥ 1`, every job has `m` unit operations,
the arcs are well formed (they name jobs and are acyclic), and the precedence relation is an
in-tree: each job has at most one immediate successor. -/
def WellFormed (i : UnitFlowShopInTreeReleaseMakespanInstance) : Prop :=
  0 < i.1 ∧ UnitJobs i.1 (i.2.1.map Prod.fst) ∧ PrecWellFormed i.2.1.length i.2.2.1 ∧
    let lt := Relation.TransGen (Prec (n := i.2.1.length) i.2.2.1)
    ∀ j a b, (lt j a ∧ ∀ c, ¬ (lt j c ∧ lt c a)) → (lt j b ∧ ∀ c, ¬ (lt j c ∧ lt c b)) →
      a = b

/-- Some schedule starts no operation of job `j` before `r_j` and completes every operation by
time `K` (makespan `max_j C_j ≤ K`). -/
def UnitFlowShopInTreeReleaseMakespanFeasible
    (i : UnitFlowShopInTreeReleaseMakespanInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    (∀ (k : Fin i.1) (j : Fin i.2.1.length), (i.2.1.getD j ([], 0)).2 ≤ σ k j) ∧
      ∀ k j, σ k j + 1 ≤ i.2.2.2

open Classical in
/-- FLOW SHOP F|p_ij=1;intree;r_i|Cmax as a decision problem over bitstrings. -/
noncomputable def unitFlowShopInTreeReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopInTreeReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ UnitFlowShopInTreeReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopInTreeReleaseMakespan
