/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP O|p_ij=1;prec;no-wait|ΣC_i is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Open-shop problems with no-wait", minimal NP-hard entry
`O | p_ij = 1; prec; no-wait | Σ C_i`, NP-hard in the strong sense, credited to Lenstra and
Rinnooy Kan (1978));
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence constraints",
Operations Research 26(1) (1978), 22-35, doi:10.1287/opre.26.1.22.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopNoWaitPrecedenceTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan
  (UnitFlowShopPrecedenceMakespanInstance WellFormed)
open MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-!
# NO-WAIT OPEN SHOP O|p_ij=1;prec;no-wait|ΣC_i is NP-complete

INSTANCE: a number `m ≥ 1` of machines `M_1, …, M_m` in an open shop, `n` jobs, each job `j`
consisting of `m` operations `O_j1, …, O_jm` with processing times `p_jk = 1`, where `O_jk` is
processed on `M_k` and the operations of a job may be processed in any order, but no two of them
at the same time; an acyclic precedence relation on the jobs (if `i` precedes `j`, then no
operation of `j` starts before every operation of `i` is completed); and a bound `K`. Each
machine processes at most one operation at a time, and no job waits: there is no waiting time
between consecutive operations of a job. QUESTION: is there a schedule whose total completion
time `Σ_j C_j` is at most `K`, where `C_j` is the completion time of job `j` (of its last
operation)?

The instance (with `K` bounding the total completion time), its well-formedness (`m ≥ 1`, `m`
unit operations per listed job, acyclic precedence arcs; `UnitFlowShopPrecedenceMakespanWanted`)
and the open-shop schedule `IsUnitOpenShopSchedule` (integer start times `σ k j` of operation
`O_jk`; `UnitOpenShopPrecedenceMakespanWanted`) are reused. A job's `m` unit operations start at
distinct integer times, so the job waits between none of them exactly when they occupy the `m`
consecutive unit slots starting at some time `s`: `s ≤ σ k j < s + m` for every machine `k`. The
completion time of job `j` is `C_j = max_k (σ k j + 1)` (a supremum over the `m ≥ 1` machines).
Numbers use the binary encoding.

Brucker and Knust classify the problem as NP-hard in the strong sense, crediting Lenstra and
Rinnooy Kan, who prove the parallel-machine problem with unit-time jobs, precedence constraints
and total completion time NP-hard. Membership in NP is the certificate argument: in a schedule of
total completion time at most `K` every start time is below `K`, and the `n · m` start times are
checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some no-wait open-shop schedule has total completion time at most `K`: each job's
operations fill `m` consecutive unit slots, and `Σ_j max_k (σ k j + 1) ≤ K`. -/
def UnitOpenShopNoWaitPrecedenceTotalCompletionFeasible
    (i : UnitFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsUnitOpenShopSchedule i.1 i.2.1.length i.2.2.1 σ ∧
    (∀ j, ∃ s, ∀ k, s ≤ σ k j ∧ σ k j < s + i.1) ∧
    ∑ j, Finset.univ.sup (fun k => σ k j + 1) ≤ i.2.2.2

open Classical in
/-- NO-WAIT OPEN SHOP O|p_ij=1;prec;no-wait|ΣC_i as a decision problem over bitstrings. -/
noncomputable def unitOpenShopNoWaitPrecedenceTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopNoWaitPrecedenceTotalCompletionFeasible i)
  | none => false

/-- **NO-WAIT OPEN SHOP O|p_ij=1;prec;no-wait|ΣC_i is NP-complete.** Source: Brucker and
Knust's classification (strongly NP-hard), citing Lenstra and Rinnooy Kan (1978); membership in
NP is the certificate argument in the module docstring. -/
public theorem_wanted unitOpenShopNoWaitPrecedenceTotalCompletion_npComplete :
    unitOpenShopNoWaitPrecedenceTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitOpenShopNoWaitPrecedenceTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopNoWaitPrecedenceTotalCompletion
