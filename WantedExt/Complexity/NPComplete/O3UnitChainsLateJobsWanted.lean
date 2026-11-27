/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP `O3|p_ij=1;chains|ΣU_i` is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `o_nop` (open shop problems without
preemption), entry `O3|p_ij=1;chains|ΣU_i` (minimal NP-hard in the strong sense, citing
Timkovsky 2003);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (abstract only; the full text was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import WantedExt.Complexity.NPComplete.F3UnitChainsLateJobsWanted
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted
public import WantedExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.O3UnitChainsLateJobs

open F3UnitChainsLateJobs (F3UnitChainsLateJobsInstance WellFormed)
open UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)
open MultipurposeFlowShopPrecedenceMakespan (completionTime)

/-!
# OPEN SHOP `O3|p_ij=1;chains|ΣU_i` is NP-complete

There are three machines `M₁, M₂, M₃` in an open shop and `n` jobs. Each job `j` consists of
three operations `O_j1, O_j2, O_j3` with unit processing times (`p_ij = 1`); `O_jk` is processed
on `M_k`; the operations of a job may be processed in any order, but no two of them at the same
time. Each machine processes at most one operation at a time. The jobs are subject to precedence
constraints forming chains (every job has at most one immediate predecessor and at most one
immediate successor): if `i` precedes `j`, then no operation of `j` starts before every
operation of `i` is completed. Each job `j` has a due date `d_j`, and `C_j` is the completion
time of its last operation; job `j` is late when `C_j > d_j`. Given an integer `K`, the question
is whether some feasible schedule has at most `K` late jobs (`ΣU_j ≤ K`).

This is Brucker and Knust's `O3|p_ij=1;chains|ΣU_i`, which they classify as minimal NP-hard in the
strong sense, citing Timkovsky (2003), whose abstract describes reductions between identical
parallel machines and unit-time shops and between preemptions and chains; the full text was not
available. It differs from the flow shop `F3|p_ij=1;chains|ΣU_i` (`F3UnitChainsLateJobsWanted`) only
in the machine order of a job's operations, which is free here. The instance type (the due dates
`d_j` of the jobs `0, …, n - 1`, one listed number per job; the chain arcs `(i, j)`, job `i`
immediately preceding job `j`; the bound `K`) and the well-formedness (the arcs form chains: they
name jobs, no job has two immediate successors or two immediate predecessors, no cycle) are reused
from that module. Enforcing the listed immediate precedences enforces the whole chain order, its
transitive closure. A schedule gives each operation `O_jk` an integer start time `σ k j ∈ ℕ` and is
the repository's unit-time open-shop schedule
`UnitOpenShopOutTreeMaxLateness.IsUnitOpenShopSchedule` on three machines (on each machine, and
within each job, operations start at pairwise different times; a job starts each operation only
after every operation of its predecessors is completed). The completion time of job `j` is
`MultipurposeFlowShopPrecedenceMakespan.completionTime`, the latest completion `σ k j + 1` of its
operations. Integer start times are no restriction for unit operations and integer due dates.

Numbers use the binary encoding; the problem is NP-hard in the strong sense, with every job listed.
Membership in NP: deleting a time unit at which no operation runs and shifting every later operation
one unit earlier keeps a schedule feasible and no completion time grows, so some schedule with all
start times below `3n` has at most as many late jobs as any schedule, and its `3n` start times are a
polynomial certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some unit-time three-machine open-shop schedule obeying the chain arcs has at most `K` late
jobs: jobs `j` whose completion time `C_j` (the latest `σ k j + 1`) exceeds the due date `d_j`. -/
def O3UnitChainsLateJobsFeasible (i : F3UnitChainsLateJobsInstance) : Prop :=
  ∃ σ : Fin 3 → Fin i.1.length → ℕ, IsUnitOpenShopSchedule 3 i.1.length i.2.1 σ ∧
    (Finset.univ.filter fun j : Fin i.1.length =>
      i.1.get j < completionTime (fun _ _ => 1) (fun j k => σ k j) j).card ≤ i.2.2

open Classical in
/-- `O3|p_ij=1;chains|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def o3UnitChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ O3UnitChainsLateJobsFeasible i)
  | none => false

/-- **OPEN SHOP `O3|p_ij=1;chains|ΣU_i` is NP-complete.** Source: Brucker and Knust's
classification (strongly NP-hard), citing Timkovsky (2003). -/
public theorem_wanted o3UnitChainsLateJobs_npComplete :
    o3UnitChainsLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L o3UnitChainsLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.O3UnitChainsLateJobs
