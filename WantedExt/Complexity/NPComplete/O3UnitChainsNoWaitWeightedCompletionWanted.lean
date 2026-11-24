/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|Σw_iC_i` is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `o_now` (open-shop problems with
no-wait), entry `O3|p_ij=1;chains;no-wait|Σw_iC_i` (minimal NP-hard in the strong sense, citing
Timkovsky 2003);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (only the abstract and introduction were available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.F3UnitChainsWeightedCompletionWanted
public import WantedExt.Complexity.NPComplete.O3UnitChainsNoWaitLateJobsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.O3UnitChainsNoWaitWeightedCompletion

open F3UnitChainsWeightedCompletion (F3UnitChainsWeightedCompletionInstance WellFormed)
open O3UnitChainsNoWaitLateJobs (IsNoWaitSchedule)

/-!
# NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|Σw_iC_i` is NP-complete

There are three machines `M₁, M₂, M₃` in an open shop and `n` jobs. Each job `i` consists of
three operations `O_i1, O_i2, O_i3` with unit processing times (`p_ij = 1`), `O_ij` processed on
`M_j`; the operations of a job may be processed in any order, but no two of them at the same
time, and each machine processes at most one operation at a time. No-wait: each operation of a
job other than its first starts exactly when the preceding operation of the job is completed.
The jobs are subject to precedence constraints forming chains (every job has at most one
immediate predecessor and at most one immediate successor): if `i` precedes `j`, then no
operation of `j` starts before every operation of `i` is completed. `C_i` is the completion time
of the last operation of job `i`. Each job has a weight `w_i`. Given an integer `K`, the
question is whether some feasible schedule has total weighted completion time `Σw_iC_i ≤ K`.

The instance (weights `w_i` of the jobs listed one per entry, chain arcs, `K`) and its
well-formedness (the arcs form chains on the jobs) are those of `F3|p_ij=1;chains|Σw_iC_i`
(`F3UnitChainsWeightedCompletionWanted`).
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

/-- Some no-wait schedule has total weighted completion time at most `K`, with
`C_j = S j + 3`. -/
def O3UnitChainsNoWaitWeightedCompletionFeasible (i : F3UnitChainsWeightedCompletionInstance) :
    Prop :=
  ∃ (S : Fin i.1.length → ℕ) (σ : Fin 3 → Fin i.1.length → ℕ),
    IsNoWaitSchedule 3 i.1.length i.2.1 S σ ∧ ∑ j, i.1.get j * (S j + 3) ≤ i.2.2

open Classical in
/-- `O3|p_ij=1;chains;no-wait|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def o3UnitChainsNoWaitWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ O3UnitChainsNoWaitWeightedCompletionFeasible i)
  | none => false

/-- **NO-WAIT OPEN SHOP `O3|p_ij=1;chains;no-wait|Σw_iC_i` is NP-complete.** Source: Brucker and
Knust's classification (strongly NP-hard), citing Timkovsky (2003); membership in NP is the
certificate argument in `O3UnitChainsNoWaitLateJobsWanted`. -/
public theorem_wanted o3UnitChainsNoWaitWeightedCompletion_npComplete :
    o3UnitChainsNoWaitWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L o3UnitChainsNoWaitWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.O3UnitChainsNoWaitWeightedCompletion
