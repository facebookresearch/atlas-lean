/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O2|chains|Cmax is NP-complete

Source:
V. S. Tanaev, Y. N. Sotskov and V. A. Strusevich, *Scheduling Theory. Multi-Stage Systems*,
Mathematics and its Applications 285, Kluwer Academic Publishers, Dordrecht (1994),
doi:10.1007/978-94-011-1192-8 (not available here); recorded as strongly NP-hard (a minimal
NP-hard problem) in P. Brucker and S. Knust, *Complexity results for scheduling problems*, class
"Open-shop problems without preemption" (University of Osnabrück,
http://www.mathematik.uni-osnabrueck.de/research/OR/class/), problem `O2|chains|C_max`,
credited to Tanaev et al. (1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.F3UnitChainsLateJobsWanted
public import WantedExt.Complexity.NPComplete.OpenShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopChains

open MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling (OpenShopSchedulingInstance)
open MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopScheduling
  (IsOpenShopSchedule taskLength)
open MetaMathlibExt.Complexity.NPComplete.F3UnitChainsLateJobs (ChainsWellFormed)

/-!
# OPEN SHOP O2|chains|Cmax is NP-complete

INSTANCE: an open shop with two machines `M_1, M_2` and jobs `1, …, n`; job `i` consists of two
operations `O_i1, O_i2` with processing times `p_i1, p_i2 ∈ ℤ₀⁺`, `O_ij` processed on `M_j`, in
either order but not at the same time; each machine processes at most one operation at a time;
precedence constraints forming chains (every job has at most one immediate predecessor and at
most one immediate successor): if `i` precedes `j`, no operation of `j` starts before every
operation of `i` is completed; a bound `K`. QUESTION: is there a schedule whose makespan, the
largest completion time of an operation, is at most `K`?

This is Brucker and Knust's `O2|chains|C_max`, listed as minimal strongly NP-hard and credited to
Tanaev, Sotskov and Strusevich (1994). It is OPEN-SHOP SCHEDULING (`OpenShopSchedulingWanted`)
with `m = 2` processors and chain precedences. The instance extends an OPEN-SHOP SCHEDULING
instance (`m`, the jobs, each listed as the list of its task lengths `[p_i1, p_i2]`, and the
deadline `D = K`) by the chain arcs `(i, j)` (job `i` immediately precedes job `j`). The schedule
is `NoWaitFlowShopScheduling.IsOpenShopSchedule` (each machine's start times are pairwise distinct
and a later task starts after an earlier one completes, the tasks of a job occupy disjoint
intervals, and every task completes by `K`, the makespan bound). `WellFormed` keeps the parent's
conditions (`m ≥ 1`, `m` tasks per job, `K ≥ 1`), adds `m = 2`, and requires the arcs to form
chains on the jobs (`F3UnitChainsLateJobs.ChainsWellFormed`: distinct arcs naming jobs, no job
with two immediate successors or two immediate predecessors, no cycle). Requiring every arc
`(i, j)` to be respected makes every pair in the generated order respected. Binary encoding of
all numbers. Membership in NP: the start times are a certificate, each below `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: an OPEN-SHOP SCHEDULING instance (the number `m` of machines, the jobs as lists
of task lengths, the bound `K`) and the chain arcs `(i, j)`. -/
abbrev TwoProcessorOpenShopChainsInstance := OpenShopSchedulingInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed OPEN-SHOP SCHEDULING instance with two
machines, whose arcs form chains on the jobs. -/
def WellFormed (i : TwoProcessorOpenShopChainsInstance) : Prop :=
  NoWaitFlowShopScheduling.WellFormed i.1 ∧ i.1.1 = 2 ∧ ChainsWellFormed i.1.2.1.length i.2

/-- Some open-shop schedule meeting the makespan bound `K` respects the chains: if job `a`
immediately precedes job `b`, every task of `b` starts after every task of `a` is completed. -/
def TwoProcessorOpenShopChainsFeasible (i : TwoProcessorOpenShopChainsInstance) : Prop :=
  ∃ σ : Fin i.1.1 → Fin i.1.2.1.length → ℕ, IsOpenShopSchedule i.1 σ ∧
    ∀ a b : Fin i.1.2.1.length, ((a : ℕ), (b : ℕ)) ∈ i.2 →
      ∀ p q, σ p a + taskLength i.1 p a ≤ σ q b

open Classical in
/-- OPEN SHOP `O2|chains|C_max` as a decision problem over bitstrings. -/
noncomputable def twoProcessorOpenShopChainsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorOpenShopChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorOpenShopChainsFeasible i)
  | none => false

/-- **OPEN SHOP `O2|chains|C_max` is NP-complete.** Source: Tanaev, Sotskov and Strusevich
(1994), as recorded in the Brucker-Knust classification of scheduling problems. -/
public theorem_wanted twoProcessorOpenShopChains_npComplete :
    twoProcessorOpenShopChainsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorOpenShopChainsDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopChains
