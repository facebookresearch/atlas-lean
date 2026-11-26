/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP `F3|p_ij=1;chains|ΣU_i` is NP-complete

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036; recorded as
strongly NP-hard (a minimal NP-hard problem) in P. Brucker and S. Knust, *Complexity results for
scheduling problems*, class "Flow-shop problems without preemption" (University of Osnabrück,
http://www2.informatik.uni-osnabrueck.de/knust/class/), problem `F3|p_ij=1;chains|ΣU_i`, credited
to Brucker and Knust (1999).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.F3UnitChainsLateJobs

/-!
# FLOW SHOP `F3|p_ij=1;chains|ΣU_i` is NP-complete

There are three machines `M₁, M₂, M₃` in a flow shop and `n` jobs. Each job `i` consists of three
operations `O_i1, O_i2, O_i3` with unit processing times (`p_ij = 1`); `O_ij` is processed on
`M_j`, and `O_i,j+1` cannot start before `O_ij` is completed. Each machine processes at most one
operation at a time. The jobs are subject to precedence constraints forming chains (every job
has at most one immediate predecessor and at most one immediate successor): if `i` precedes `j`,
then `j` cannot start before `i` is completed. Each job has a due date `d_i`, and `C_i` is the
completion time of its last operation; job `i` is late when `C_i > d_i`. Given an integer `K`,
the question is whether some feasible schedule has at most `K` late jobs (`ΣU_i ≤ K`).

Machines are `Fin 3` (`0, 1, 2` for `M₁, M₂, M₃`), jobs `Fin n`. Time is discrete: with unit
operations and integer data, schedules with integer start times are no restriction. Binary
encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance `(d, chains, K)`: the due dates `d_i` of the jobs `0, …, n - 1` (`n` is the
length of the list), the chain arcs `(i, j)` (job `i` immediately precedes job `j`), and the
bound `K`. -/
abbrev F3UnitChainsLateJobsInstance := List ℕ × List (ℕ × ℕ) × ℕ

/-- The arcs form chains on the jobs `0, …, n - 1`: every arc joins two different jobs, no job
has two immediate successors or two immediate predecessors, and there is no cycle. -/
def ChainsWellFormed (n : ℕ) (chains : List (ℕ × ℕ)) : Prop :=
  chains.Nodup ∧ (∀ a ∈ chains, a.1 < n ∧ a.2 < n) ∧
    (∀ a ∈ chains, ∀ b ∈ chains, a.1 = b.1 → a = b) ∧
    (∀ a ∈ chains, ∀ b ∈ chains, a.2 = b.2 → a = b) ∧
    ∀ i, ¬ Relation.TransGen (fun i j => (i, j) ∈ chains) i i

/-- `S i k` is a feasible schedule (start time of operation `O_i,k+1` of job `i` on machine
`M_k+1`, every operation of length `1`): each job's operations run in machine order, each machine
runs one operation at a time, and if `i` immediately precedes `j`, then `j` starts on `M₁` only
after `i` is completed on `M₃`. -/
def IsSchedule (n : ℕ) (chains : List (ℕ × ℕ)) (S : Fin n → Fin 3 → ℕ) : Prop :=
  (∀ i, S i 0 + 1 ≤ S i 1 ∧ S i 1 + 1 ≤ S i 2) ∧
    (∀ k i i', i ≠ i' → S i k + 1 ≤ S i' k ∨ S i' k + 1 ≤ S i k) ∧
    ∀ i j : Fin n, ((i : ℕ), (j : ℕ)) ∈ chains → S i 2 + 1 ≤ S j 0

/-- Well-formedness: the arcs form chains on the jobs. -/
def WellFormed (i : F3UnitChainsLateJobsInstance) : Prop :=
  ChainsWellFormed i.1.length i.2.1

/-- Some feasible schedule has at most `K` late jobs: jobs `i` with completion time
`C_i = S i 2 + 1` greater than the due date `d_i`. -/
def F3UnitChainsLateJobsFeasible (i : F3UnitChainsLateJobsInstance) : Prop :=
  ∃ S : Fin i.1.length → Fin 3 → ℕ, IsSchedule i.1.length i.2.1 S ∧
    (Finset.univ.filter fun j : Fin i.1.length => i.1.get j < S j 2 + 1).card ≤ i.2.2

open Classical in
/-- `F3|p_ij=1;chains|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def f3UnitChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ F3UnitChainsLateJobsFeasible i)
  | none => false

/-- **FLOW SHOP `F3|p_ij=1;chains|ΣU_i` is NP-complete.** Source: Brucker and Knust (1999),
as recorded in the Brucker-Knust classification of scheduling problems. -/
public theorem_wanted f3UnitChainsLateJobs_npComplete :
    f3UnitChainsLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L f3UnitChainsLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.F3UnitChainsLateJobs
