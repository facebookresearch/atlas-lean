/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|ΣU_i` is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `o_now` (open-shop problems with
no-wait), entry `O3|p_ij=1;chains;no-wait|ΣU_i` (minimal NP-hard in the strong sense, citing
Timkovsky 2003);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (only the abstract and introduction were available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.F3UnitChainsLateJobsWanted
public import WantedExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.O3UnitChainsNoWaitLateJobs

open F3UnitChainsLateJobs (F3UnitChainsLateJobsInstance WellFormed)
open UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-!
# NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|ΣU_i` is NP-complete

There are three machines `M₁, M₂, M₃` in an open shop and `n` jobs. Each job `i` consists of
three operations `O_i1, O_i2, O_i3` with unit processing times (`p_ij = 1`), `O_ij` processed on
`M_j`; the operations of a job may be processed in any order, but no two of them at the same
time, and each machine processes at most one operation at a time. No-wait: each operation of a
job other than its first starts exactly when the preceding operation of the job is completed.
The jobs are subject to precedence constraints forming chains (every job has at most one
immediate predecessor and at most one immediate successor): if `i` precedes `j`, then no
operation of `j` starts before every operation of `i` is completed. Each job has a due date
`d_i`, and `C_i` is the completion time of its last operation; job `i` is late when `C_i > d_i`.
Given an integer `K`, the question is whether some feasible schedule has at most `K` late jobs
(`ΣU_i ≤ K`).

The instance (due dates `d_i` of the jobs listed one per entry, chain arcs, `K`) and its
well-formedness (the arcs form chains on the jobs) are those of the flow shop
`F3|p_ij=1;chains|ΣU_i` (`F3UnitChainsLateJobsWanted`). Machines are `Fin 3`, jobs `Fin n`. A
schedule gives operation `O_jk` the start time `σ k j`; `σ` is a unit-time open-shop schedule
obeying the chain arcs (`UnitOpenShopOutTreeMaxLateness.IsUnitOpenShopSchedule`: the operations
on one machine, and the operations of one job, start at pairwise different times, and if `i`
precedes `j`, every operation of `j` starts after every operation of `i` is completed). No-wait
is stated with a start time `S j` of job `j`: all its operations start in `[S j, S j + 3)`.
Since they start at three different times, they start exactly at `S j`, `S j + 1`, `S j + 2`,
each one when the previous one is completed, and job `j` completes at `C_j = S j + 3`.

Time is discrete: rounding all start times of a schedule down keeps every constraint, no-wait
included, and increases no completion time. Deleting a time unit in which no machine works, and
moving everything after it one unit earlier, also keeps a schedule feasible and increases no
completion time, so some optimal schedule has all start times below `3n`. Membership in NP is
therefore the certificate argument: the start times `S` and `σ` are checked in polynomial time.
Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `σ k j` (start of job `j`'s unit operation on machine `k`) is a no-wait unit-time open-shop
schedule on `m` machines for the precedence arcs `A`, job `j` starting at `S j`: `σ` is a
unit-time open-shop schedule (`UnitOpenShopOutTreeMaxLateness.IsUnitOpenShopSchedule`), and every
operation of job `j` starts in `[S j, S j + m)`, so that the `m` operations of the job run back to
back from `S j` on. -/
def IsNoWaitSchedule (m n : ℕ) (A : List (ℕ × ℕ)) (S : Fin n → ℕ) (σ : Fin m → Fin n → ℕ) :
    Prop :=
  IsUnitOpenShopSchedule m n A σ ∧ ∀ k j, S j ≤ σ k j ∧ σ k j < S j + m

/-- Some no-wait schedule has at most `K` late jobs: jobs `j` with completion time
`C_j = S j + 3` greater than the due date `d_j`. -/
def O3UnitChainsNoWaitLateJobsFeasible (i : F3UnitChainsLateJobsInstance) : Prop :=
  ∃ (S : Fin i.1.length → ℕ) (σ : Fin 3 → Fin i.1.length → ℕ),
    IsNoWaitSchedule 3 i.1.length i.2.1 S σ ∧
      (Finset.univ.filter fun j : Fin i.1.length => i.1.get j < S j + 3).card ≤ i.2.2

open Classical in
/-- `O3|p_ij=1;chains;no-wait|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def o3UnitChainsNoWaitLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ O3UnitChainsNoWaitLateJobsFeasible i)
  | none => false

/-- **NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|ΣU_i` is NP-complete.** Source: Brucker and
Knust's classification (strongly NP-hard), citing Timkovsky (2003); membership in NP is the
certificate argument in the module docstring. -/
public theorem_wanted o3UnitChainsNoWaitLateJobs_npComplete :
    o3UnitChainsNoWaitLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L o3UnitChainsNoWaitLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.O3UnitChainsNoWaitLateJobs
