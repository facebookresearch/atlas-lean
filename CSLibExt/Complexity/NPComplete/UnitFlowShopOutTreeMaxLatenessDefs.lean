/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP F|p_ij=1;outtree|Lmax: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Flow-shop problems without preemption", minimal NP-hard entry
`F | p_ij = 1; outtree | L_max`); P. Brucker and S. Knust, "Complexity results for
single-machine problems with positive finish-start time-lags", Computing 63 (1999), 299-316,
doi:10.1007/s006070050036.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLateness

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan
  (Prec PrecWellFormed IsSchedule UnitJobs)

/-- An instance `(m, J, A, K)`: the number of machines `m`, the jobs `J` (job `j` listed as its
processing times `(p_j1, …, p_jm)` and its due date `d_j`), the precedence arcs `A` (`(i, j)`:
job `i` precedes job `j`), and the bound `K`; `d_j` and `K` are integers given as pairs `(a, b)`
standing for `a - b`. -/
abbrev UnitFlowShopOutTreeMaxLatenessInstance :=
  ℕ × List (List ℕ × (ℕ × ℕ)) × List (ℕ × ℕ) × (ℕ × ℕ)

/-- The integer `a - b` encoded by the pair `(a, b)`. -/
def toInt (z : ℕ × ℕ) : ℤ := (z.1 : ℤ) - (z.2 : ℤ)

/-- Well-formedness of an instance `(m, J, A, K)`: `m ≥ 1`, every job has `m` unit operations,
the arcs are well formed (they name jobs and are acyclic), and the precedence relation is an
out-tree: each job has at most one immediate predecessor. -/
def WellFormed (i : UnitFlowShopOutTreeMaxLatenessInstance) : Prop :=
  0 < i.1 ∧ UnitJobs i.1 (i.2.1.map Prod.fst) ∧ PrecWellFormed i.2.1.length i.2.2.1 ∧
    let lt := Relation.TransGen (Prec (n := i.2.1.length) i.2.2.1)
    ∀ j a b, (lt a j ∧ ∀ c, ¬ (lt a c ∧ lt c j)) → (lt b j ∧ ∀ c, ¬ (lt b c ∧ lt c j)) →
      a = b

/-- Some schedule completes every operation of every job `j` by time `d_j + K` (maximum
lateness `max_j (C_j - d_j) ≤ K`). -/
def UnitFlowShopOutTreeMaxLatenessFeasible (i : UnitFlowShopOutTreeMaxLatenessInstance) :
    Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    ∀ (k : Fin i.1) (j : Fin i.2.1.length),
      ((σ k j + 1 : ℕ) : ℤ) - toInt (i.2.1.getD j ([], (0, 0))).2 ≤ toInt i.2.2.2

open Classical in
/-- FLOW SHOP F|p_ij=1;outtree|Lmax as a decision problem over bitstrings. -/
noncomputable def unitFlowShopOutTreeMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopOutTreeMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ UnitFlowShopOutTreeMaxLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLateness
