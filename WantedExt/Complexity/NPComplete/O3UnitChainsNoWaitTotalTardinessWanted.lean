/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|ΣT_i` is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `o_now` (open-shop problems with
no-wait), entry `O3|p_ij=1;chains;no-wait|ΣT_i` (minimal NP-hard in the strong sense, citing
Timkovsky 2003);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (only the abstract and introduction were available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.O3UnitChainsNoWaitTotalTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.O3UnitChainsNoWaitTotalTardiness

open F3UnitChainsLateJobs (F3UnitChainsLateJobsInstance WellFormed)
open O3UnitChainsNoWaitLateJobs (IsNoWaitSchedule)

/-!
# NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|ΣT_i` is NP-complete

There are three machines `M₁, M₂, M₃` in an open shop and `n` jobs. Each job `i` consists of
three operations `O_i1, O_i2, O_i3` with unit processing times (`p_ij = 1`), `O_ij` processed on
`M_j`; the operations of a job may be processed in any order, but no two of them at the same
time, and each machine processes at most one operation at a time. No-wait: each operation of a
job other than its first starts exactly when the preceding operation of the job is completed.
The jobs are subject to precedence constraints forming chains (every job has at most one
immediate predecessor and at most one immediate successor): if `i` precedes `j`, then no
operation of `j` starts before every operation of `i` is completed. `C_i` is the completion time
of the last operation of job `i`. Each job has a due date `d_i` and tardiness
`T_i = max(0, C_i - d_i)`. Given an integer `K`, the question is whether some feasible schedule
has total tardiness `ΣT_i ≤ K`.

The instance (due dates `d_i` of the jobs listed one per entry, chain arcs, `K`) and its
well-formedness (the arcs form chains on the jobs) are those of `F3|p_ij=1;chains|ΣU_i`
(`F3UnitChainsLateJobsWanted`), as for `O3|p_ij=1;chains;no-wait|ΣU_i`
(`O3UnitChainsNoWaitLateJobsWanted`).
The no-wait schedule is that of `O3|p_ij=1;chains;no-wait|ΣU_i`
(`O3UnitChainsNoWaitLateJobs.IsNoWaitSchedule` with `m = 3`): `σ k j` is the start time of
operation `O_jk`, the operations on one machine and the operations of one job start at pairwise
different times, chain arcs are obeyed, and all operations of job `j` start in
`[S j, S j + 3)`, so they run back to back and `C_j = S j + 3`. Time is discrete and some optimal
schedule has all start times below `3n`, as explained in `O3UnitChainsNoWaitLateJobsWanted`.
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

/-- **NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|ΣT_i` is NP-complete.** Source: Brucker and
Knust's classification (strongly NP-hard), citing Timkovsky (2003); membership in NP is the
certificate argument in `O3UnitChainsNoWaitLateJobsWanted`. -/
public theorem_wanted o3UnitChainsNoWaitTotalTardiness_npComplete :
    o3UnitChainsNoWaitTotalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L o3UnitChainsNoWaitTotalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.O3UnitChainsNoWaitTotalTardiness
