/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O|p_ij=1;prec|Cmax is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Open-shop problems without preemption", minimal NP-hard entry
`O | p_ij = 1; prec | C_max`, NP-hard in the strong sense, credited to Timkovsky (2003));
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanWanted
public import WantedExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopPrecedenceMakespan

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan
  (UnitFlowShopPrecedenceMakespanInstance WellFormed)
open MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-!
# OPEN SHOP O|p_ij=1;prec|Cmax is NP-complete

INSTANCE: a number `m ≥ 1` of machines `M_1, …, M_m` in an open shop, `n` jobs, each job `j`
consisting of `m` operations `O_j1, …, O_jm` with processing times `p_jk = 1`, where `O_jk` is
processed on `M_k` and the operations of a job may be processed in any order, but no two of them
at the same time; an acyclic precedence relation on the jobs (if `i` precedes `j`, then no
operation of `j` starts before every operation of `i` is completed); and a bound `K`. Each
machine processes at most one operation at a time. QUESTION: is there a schedule whose makespan
`max_j C_j` is at most `K`, where `C_j` is the completion time of job `j` (of its last
operation)?

The instance and its well-formedness are those of the unit-time flow shop with precedence
constraints (`UnitFlowShopPrecedenceMakespanWanted`): `m ≥ 1`, each job listed with its
processing times `(p_j1, …, p_jm)`, all equal to `1` (`UnitJobs`), and precedence arcs `(i, j)`
that name jobs and generate an acyclic relation (`PrecWellFormed`). Machines are `Fin m` and jobs
`Fin n` for `n` listed jobs. Only the schedule differs: in an open shop the operations of a job
have no prescribed order. A schedule gives each operation an integer start time: with unit
lengths and integer data, rounding the start times of any schedule down keeps every constraint,
and two unit operations overlap exactly when they start together. The schedule predicate is
`UnitOpenShopOutTreeMaxLateness.IsUnitOpenShopSchedule`, reused from
`UnitOpenShopOutTreeMaxLatenessWanted`. Numbers use the binary encoding.

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

/-- Some open-shop schedule completes every operation by time `K` (makespan
`max_j C_j ≤ K`). -/
def UnitOpenShopPrecedenceMakespanFeasible (i : UnitFlowShopPrecedenceMakespanInstance) :
    Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsUnitOpenShopSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    ∀ k j, σ k j + 1 ≤ i.2.2.2

open Classical in
/-- OPEN SHOP O|p_ij=1;prec|Cmax as a decision problem over bitstrings. -/
noncomputable def unitOpenShopPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopPrecedenceMakespanFeasible i)
  | none => false

/-- **OPEN SHOP O|p_ij=1;prec|Cmax is NP-complete.** Source: Brucker and Knust's classification
(strongly NP-hard), citing Timkovsky (2003); membership in NP is the certificate argument in the
module docstring. -/
public theorem_wanted unitOpenShopPrecedenceMakespan_npComplete :
    unitOpenShopPrecedenceMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitOpenShopPrecedenceMakespanDec

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopPrecedenceMakespan
