/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP F|p_ij=1;prec|Cmax is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan

/-!
# FLOW SHOP F|p_ij=1;prec|Cmax is NP-complete

INSTANCE: a number `m ≥ 1` of machines `M_1, …, M_m` in a flow shop, `n` jobs, each job `j`
consisting of `m` operations `O_j1, …, O_jm` with processing times `p_jk = 1`, where `O_jk` is
processed on `M_k` and `O_j,k+1` cannot start before `O_jk` is completed; an acyclic
precedence relation on the jobs (if `i` precedes `j`, then no operation of `j` starts before
every operation of `i` is completed); and a bound `K`. Each machine processes at most one
operation at a time. QUESTION: is there a schedule whose makespan `max_j C_j` is at most `K`,
where `C_j` is the completion time of job `j`?

Each job is listed with its processing times `(p_j1, …, p_jm)`, all equal to `1`, as in the
flow-shop encoding of `FlowShopSchedulingWanted`. Machines are `Fin m` (`M_1, …, M_m` as
`0, …, m - 1`) and jobs `Fin n` for `n` listed jobs; the precedence relation is given by its arcs
`(i, j)` and is the relation they generate (`Relation.TransGen`). A schedule gives each operation
an integer start time: with unit lengths and integer data, rounding the start times of any
schedule down keeps every constraint, and two unit operations on one machine overlap exactly when
they start together. Numbers use the binary encoding.

Brucker and Knust classify the problem as NP-hard (in the strong sense). Membership in NP is the
certificate argument: the `n · m` start times of a schedule, each below `K`, are checked in
polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **FLOW SHOP F|p_ij=1;prec|Cmax is NP-complete.** Source: Brucker and Knust's
classification (strongly NP-hard), citing Leung, Vornberger and Witthoff (1984) and Timkovsky
(2003); membership in NP is the certificate argument in the module docstring. -/
public theorem_wanted unitFlowShopPrecedenceMakespan_npComplete :
    unitFlowShopPrecedenceMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitFlowShopPrecedenceMakespanDec

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan
