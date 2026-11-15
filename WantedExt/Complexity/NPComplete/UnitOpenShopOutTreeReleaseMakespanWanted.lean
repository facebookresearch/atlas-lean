/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O|p_ij=1;outtree;r_i|Cmax is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Open-shop problems without preemption", minimal NP-hard entry
`O | p_ij = 1; outtree; r_i | C_max`, NP-hard in the strong sense, credited to Timkovsky (2003));
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLatenessWanted
public import WantedExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeReleaseMakespan

open MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-!
# OPEN SHOP O|p_ij=1;outtree;r_i|Cmax is NP-complete

INSTANCE: a number `m ≥ 1` of machines `M_1, …, M_m` in an open shop, `n` jobs, each job `j`
consisting of `m` operations `O_j1, …, O_jm` with processing times `p_jk = 1`, where `O_jk` is
processed on `M_k` and the operations of a job may be processed in any order, but no two of them
at the same time; an out-tree precedence relation on the jobs (out-forest: each job has at most
one immediate predecessor; if `i` precedes `j`, then no operation of `j` starts before every
operation of `i` is completed); a release date `r_j ∈ ℕ` for each job `j` (no operation of `j`
starts before `r_j`); and a bound `K`. Each machine processes at most one operation at a time.
QUESTION: is there a schedule whose makespan `max_j C_j` is at most `K`, where `C_j` is the
completion time of job `j` (of its last operation)?

Each job is listed with its processing times `(p_j1, …, p_jm)`, all equal to `1`, and its
release date; jobs are `Fin n` for `n` listed jobs and the precedence relation is given by its
arcs `(i, j)`. Well-formedness is that of the unit-time flow shop with out-tree precedence
(`UnitFlowShopOutTreeMaxLatenessWanted`: `m ≥ 1`, `m` unit operations per job, acyclic arcs
naming jobs, each job with at most one immediate predecessor), applied to the jobs with their
release dates set aside (that well-formedness reads neither the due dates of its own instances
nor its bound), together with a nonempty job list (the makespan `max_j C_j` is a maximum over
the jobs). The schedule is the open-shop schedule `IsUnitOpenShopSchedule` of
`UnitOpenShopOutTreeMaxLatenessWanted` (integer start times `σ k j` of operation `O_jk`; with
unit lengths and integer data, rounding start times down keeps every constraint). Numbers use
the binary encoding.

Brucker and Knust classify the problem as NP-hard in the strong sense, crediting Timkovsky.
Membership in NP is the certificate argument: the `n · m` start times of a schedule, each below
`K`, are checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance `(m, J, A, K)`: the number of machines `m`, the jobs `J` (job `j` listed as its
processing times `(p_j1, …, p_jm)` and its release date `r_j`), the precedence arcs `A`
(`(i, j)`: job `i` precedes job `j`), and the bound `K`. -/
abbrev UnitOpenShopOutTreeReleaseMakespanInstance :=
  ℕ × List (List ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance `(m, J, A, K)`: well-formed for the unit-time out-tree flow
shop once the release dates are set aside (`m ≥ 1`, every job has `m` unit operations, the arcs
name jobs and are acyclic, and each job has at most one immediate predecessor), and there is at
least one job. -/
def WellFormed (i : UnitOpenShopOutTreeReleaseMakespanInstance) : Prop :=
  UnitFlowShopOutTreeMaxLateness.WellFormed
    (i.1, i.2.1.map (fun job => (job.1, (0, 0))), i.2.2.1, (0, 0)) ∧ i.2.1 ≠ []

/-- Some open-shop schedule starts no operation of a job before its release date and completes
every operation by time `K` (makespan `max_j C_j ≤ K`). -/
def UnitOpenShopOutTreeReleaseMakespanFeasible (i : UnitOpenShopOutTreeReleaseMakespanInstance) :
    Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsUnitOpenShopSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    (∀ k j, (i.2.1.get j).2 ≤ σ k j) ∧ ∀ k j, σ k j + 1 ≤ i.2.2.2

open Classical in
/-- OPEN SHOP O|p_ij=1;outtree;r_i|Cmax as a decision problem over bitstrings. -/
noncomputable def unitOpenShopOutTreeReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitOpenShopOutTreeReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopOutTreeReleaseMakespanFeasible i)
  | none => false

/-- **OPEN SHOP O|p_ij=1;outtree;r_i|Cmax is NP-complete.** Source: Brucker and Knust's
classification (strongly NP-hard), citing Timkovsky (2003); membership in NP is the certificate
argument in the module docstring. -/
public theorem_wanted unitOpenShopOutTreeReleaseMakespan_npComplete :
    unitOpenShopOutTreeReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitOpenShopOutTreeReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeReleaseMakespan
