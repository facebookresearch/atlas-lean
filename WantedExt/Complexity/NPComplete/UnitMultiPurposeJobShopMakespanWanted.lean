/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM3|p_ij=1|Cmax is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 242, problem [SS18] JOB-SHOP
SCHEDULING, comment (equal task lengths, `m = 3`);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Computational complexity of discrete optimization
problems", Annals of Discrete Mathematics 4 (1979), 121-140,
doi:10.1016/S0167-5060(08)70821-5;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `mpm_shop` (shop problems with multi-purpose machines), Universität Osnabrück.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultiPurposeJobShopMakespan

/-!
# MULTIPURPOSE-MACHINE JOB SHOP JMPM3|p_ij=1|Cmax is NP-complete

INSTANCE: `m = 3` machines `M₁, M₂, M₃`; jobs, each a chain of `n_j ≥ 1` unit-time operations
`O_{j1}, …, O_{jn_j}`, where each operation `O_{jk}` has a nonempty set `μ_{jk}` of eligible
machines and is processed on exactly one machine of `μ_{jk}`; a bound `K`. Each machine
processes at most one operation at a time, and `O_{j,k+1}` cannot start before `O_{jk}` is
completed. QUESTION: is there a schedule whose makespan, the largest completion time of an
operation, is at most `K`?

This is the job shop with multi-purpose machines (MPM) of Brucker and Knust's classification,
`JMPM3|p_ij=1|C_max`, which lists it as minimal NP-hard in the strong sense, citing Lenstra and
Rinnooy Kan (1979). Their result is for the dedicated-machine job shop `J3|p_ij=1|C_max`
(Garey and Johnson, [SS18], comment: "If in the nonpreemptive case all tasks have the same
length, the problem is NP-complete for `m = 3`"), which is the special case in which every
`μ_{jk}` is a single machine and consecutive operations of a job have different machines.
The multi-purpose problem puts no condition on the eligible sets of consecutive operations;
with unit-time operations processed one after another, two consecutive operations of a job
never overlap, so they may use the same machine.

A schedule chooses a machine `μ t ∈ μ_{jk}` and a start time `σ t ∈ ℤ₀⁺` for every operation
`t`; operations on the same machine have different start times (with unit lengths, this is
"one operation at a time"). Start times are natural numbers: with unit operations, shifting
every operation of a feasible schedule as early as its machine order allows gives an integral
schedule with no later completion times, so this does not change the answer. The number of
machines is part of the instance, and `WellFormed` fixes it to `3`. Binary encoding of all
numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of machines; the jobs, job `j` being the list of its operations
in order, each operation given by the list of its eligible machines (numbered `1, …, m`); and
the bound `K`. -/
abbrev UnitMultiPurposeJobShopInstance := ℕ × List (List (List ℕ)) × ℕ

/-- An operation `O_{jk}` of the instance: a job `j` and a position `k < n_j`. -/
abbrev Operation (i : UnitMultiPurposeJobShopInstance) : Type :=
  (j : Fin i.2.1.length) × Fin (i.2.1.get j).length

/-- The eligible machines `μ_{jk}` of an operation. -/
def eligible (i : UnitMultiPurposeJobShopInstance) (t : Operation i) : List ℕ :=
  (i.2.1.get t.1).get t.2

/-- A schedule of the unit-time multi-purpose job shop: machine `μ t` and start time `σ t` for
every operation `t`, with every operation on an eligible machine, operations on the same
machine at different start times, and every operation of a job starting after the previous
operation of the job completes. -/
def IsUnitMPMSchedule (i : UnitMultiPurposeJobShopInstance) (μ σ : Operation i → ℕ) : Prop :=
  (∀ t, μ t ∈ eligible i t) ∧
    (∀ t t', μ t = μ t' → σ t = σ t' → t = t') ∧
    ∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 → σ ⟨j, k⟩ + 1 ≤ σ ⟨j, k'⟩

/-- An instance describes a multi-purpose job shop: every job has at least one operation, every
operation has a nonempty set of eligible machines, and every eligible machine lies in
`{1, …, m}`. -/
def IsMPMInstance (i : UnitMultiPurposeJobShopInstance) : Prop :=
  (∀ job ∈ i.2.1, job ≠ []) ∧ (∀ job ∈ i.2.1, ∀ μ ∈ job, μ ≠ []) ∧
    ∀ job ∈ i.2.1, ∀ μ ∈ job, ∀ M ∈ μ, 1 ≤ M ∧ M ≤ i.1

/-- Well-formedness of an instance: `m = 3`, and the instance describes a multi-purpose job
shop (`IsMPMInstance`). -/
def WellFormed (i : UnitMultiPurposeJobShopInstance) : Prop :=
  i.1 = 3 ∧ IsMPMInstance i

/-- Some schedule completes every operation by `K`: the last operation of every job, which
completes after the job's other operations, ends by `K`. -/
def UnitMultiPurposeJobShopMakespanFeasible (i : UnitMultiPurposeJobShopInstance) : Prop :=
  ∃ μ σ : Operation i → ℕ, IsUnitMPMSchedule i μ σ ∧
    ∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length → σ ⟨j, k⟩ + 1 ≤ i.2.2

open Classical in
/-- MULTIPURPOSE-MACHINE JOB SHOP `JMPM3|p_ij=1|C_max` as a decision problem over bitstrings. -/
noncomputable def unitMultiPurposeJobShopMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitMultiPurposeJobShopInstance) x with
  | some i => decide (WellFormed i ∧ UnitMultiPurposeJobShopMakespanFeasible i)
  | none => false

/-- **MULTIPURPOSE-MACHINE JOB SHOP `JMPM3|p_ij=1|C_max` is NP-complete.** Source: Garey and
Johnson (1979), [SS18], comment; Lenstra and Rinnooy Kan (1979); Brucker and Knust,
scheduling classification, class `mpm_shop`. -/
public theorem_wanted unitMultiPurposeJobShopMakespan_npComplete :
    unitMultiPurposeJobShopMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitMultiPurposeJobShopMakespanDec

end MetaMathlibExt.Complexity.NPComplete.UnitMultiPurposeJobShopMakespan
