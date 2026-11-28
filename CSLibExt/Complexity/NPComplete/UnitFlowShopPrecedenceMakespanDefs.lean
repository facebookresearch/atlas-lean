/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP F|p_ij=1;prec|Cmax: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Flow-shop problems without preemption", minimal NP-hard entry
`F | p_ij = 1; prec | C_max`); J. Y.-T. Leung, O. Vornberger and J. D. Witthoff, "On some
variants of the bandwidth minimization problem", SIAM Journal on Computing 13(3) (1984),
650-667, doi:10.1137/0213040; V. G. Timkovsky, "Identical parallel machines vs. unit-time
shops and preemptions vs. chains in scheduling complexity", European Journal of Operational
Research 149(2) (2003), 355-376, doi:10.1016/S0377-2217(02)00767-1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan

/-- An instance `(m, P, A, K)`: the number of machines `m`, the jobs `P` (job `j` listed by its
processing times `(p_j1, …, p_jm)`), the precedence arcs `A` (`(i, j)`: job `i` precedes job
`j`), and the bound `K`. -/
abbrev UnitFlowShopPrecedenceMakespanInstance := ℕ × List (List ℕ) × List (ℕ × ℕ) × ℕ

/-- Every listed job has `m` operations, each of processing time `1` (`p_jk = 1`). -/
def UnitJobs (m : ℕ) (P : List (List ℕ)) : Prop :=
  ∀ job ∈ P, job.length = m ∧ ∀ p ∈ job, p = 1

/-- Job `i` precedes job `j`: the arc `(i, j)` is listed. -/
def Prec {n : ℕ} (A : List (ℕ × ℕ)) (i j : Fin n) : Prop :=
  ((i : ℕ), (j : ℕ)) ∈ A

/-- Precedence arcs on `n` jobs are well formed: every arc names two jobs, and the precedence
graph is acyclic (no job precedes itself through a chain of arcs). -/
def PrecWellFormed (n : ℕ) (A : List (ℕ × ℕ)) : Prop :=
  (∀ a ∈ A, a.1 < n ∧ a.2 < n) ∧ ∀ j : Fin n, ¬ Relation.TransGen (Prec A) j j

/-- `σ k j` is the start time of operation `O_jk` (job `j` on machine `k`). `σ` is a
unit-time flow-shop schedule obeying the arcs `A`: each machine processes at most one operation
at a time, `O_j,k+1` starts after `O_jk` is completed, and if `i` precedes `j`, every operation
of `j` starts after every operation of `i` is completed. -/
def IsSchedule (m n : ℕ) (A : List (ℕ × ℕ)) (σ : Fin m → Fin n → ℕ) : Prop :=
  (∀ k, Function.Injective (σ k)) ∧
    (∀ (k : Fin m) (hk : k.1 + 1 < m) (j : Fin n), σ k j + 1 ≤ σ ⟨k.1 + 1, hk⟩ j) ∧
    ∀ i j, Prec A i j → ∀ k k', σ k i + 1 ≤ σ k' j

/-- Well-formedness of an instance `(m, P, A, K)`: `m ≥ 1`, every job has `m` unit operations,
and the arcs are well formed. -/
def WellFormed (i : UnitFlowShopPrecedenceMakespanInstance) : Prop :=
  0 < i.1 ∧ UnitJobs i.1 i.2.1 ∧ PrecWellFormed i.2.1.length i.2.2.1

/-- Some schedule completes every operation by time `K` (makespan `max_j C_j ≤ K`). -/
def UnitFlowShopPrecedenceMakespanFeasible (i : UnitFlowShopPrecedenceMakespanInstance) :
    Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    ∀ k j, σ k j + 1 ≤ i.2.2.2

open Classical in
/-- FLOW SHOP F|p_ij=1;prec|Cmax as a decision problem over bitstrings. -/
noncomputable def unitFlowShopPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ UnitFlowShopPrecedenceMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan
