/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|r_i;p_ij=1|Σw_iC_i is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
recorded in P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `JMPM2|r_i;p_ij=1|Σw_iC_i`, minimal NP-hard in the strong sense, Timkovsky (1998));
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM job shop
model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopReleaseWeightedCompletion

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule
  MPMWellFormed)

/-!
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|r_i;p_ij=1|Σw_iC_i is NP-complete

INSTANCE: `m = 2` machines `M₁, M₂`; jobs, each a chain of `n_j ≥ 1` unit-time operations
`O_{j1}, …, O_{jn_j}`, where each operation `O_{jk}` has a nonempty set `μ_{jk} ⊆ {M₁, M₂}` of
eligible machines and is processed on exactly one machine of `μ_{jk}`; for each job `j` a release
date `r_j ∈ ℤ₀⁺` and a weight `w_j ∈ ℤ₀⁺`; and a bound `K ∈ ℤ₀⁺`. Each machine processes at most
one operation at a time, `O_{j,k+1}` cannot start before `O_{jk}` is completed, and job `j`
cannot start before `r_j`. QUESTION: is there a schedule whose total weighted completion time
`Σ_j w_j C_j` is at most `K`, where `C_j` is the completion time of job `j` (of its last
operation)?

This is the job shop with multi-purpose machines (MPM) of Brucker (2004), Chapter 10, as stated in
`MultiPurposeJobShopThreeJobsWanted` (instance, operations, eligible machine sets, schedules and
`MPMWellFormed` are reused from there), with `m = 2` machines, every operation of length `1`,
release dates, and the total weighted completion time criterion. Brucker and Knust's
classification lists `JMPM2|r_i;p_ij=1|Σw_iC_i` as minimal NP-hard in the strong sense, citing
Timkovsky (1998), who reduces scheduling problems on identical parallel machines to unit-time job
shops. The dedicated-machine job shop `J2|p_ij=1;r_j|Σw_jC_j` (`UnitJobShopReleaseWeightedWanted`)
is the special case in which every `μ_{jk}` is a single machine. The model puts no condition on
the machine sets of consecutive operations of a job.

The last component `K` of the reused instance is the bound on the total weighted completion time;
the instance adds one pair `(r_j, w_j)` per job. A job cannot start before its release date, so
every operation of job `j` starts at `r_j` or later. Start times are natural numbers: shifting every
operation of a feasible schedule as early as its machine, its job predecessor and its release date
allow makes every start time `0`, a release date, or the completion time of another operation,
hence an integer, and completes no job later. Operations are listed one by one, so the instance size
counts every operation (the cited hardness is in the strong sense). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: an MPM job shop instance (the number `m` of machines, the jobs as lists of
operations `(p_{jk}, μ_{jk})`, and the bound `K` on the total weighted completion time) and one
pair `(r_j, w_j)` (release date, weight) per job. -/
abbrev MultiPurposeUnitJobShopReleaseWeightedCompletionInstance :=
  MPMJobShopInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed MPM job shop instance with `m = 2` machines
(every job nonempty, every operation with a nonempty set of eligible machines in `{1, 2}`), every
operation of length `1`, and one pair `(r_j, w_j)` per job. -/
def WellFormed (i : MultiPurposeUnitJobShopReleaseWeightedCompletionInstance) : Prop :=
  MPMWellFormed 2 i.1 ∧ (∀ job ∈ i.1.2.1, ∀ o ∈ job, o.1 = 1) ∧ i.2.length = i.1.2.1.length

/-- Some MPM job shop schedule starts every operation of job `j` at its release date `r_j` or
later and has `Σ_j w_j C_j ≤ K`, where `C j` is the completion time of the last operation of
job `j`. -/
def MultiPurposeUnitJobShopReleaseWeightedCompletionFeasible
    (i : MultiPurposeUnitJobShopReleaseWeightedCompletionInstance) : Prop :=
  ∃ a σ : Operation i.1 → ℕ, IsMPMJobShopSchedule i.1 a σ ∧
    (∀ t : Operation i.1, (i.2.getD t.1 (0, 0)).1 ≤ σ t) ∧
    ∃ C : Fin i.1.2.1.length → ℕ,
      (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
        C j = σ ⟨j, k⟩ + opLength i.1 ⟨j, k⟩) ∧
      ∑ j : Fin i.1.2.1.length, (i.2.getD j (0, 0)).2 * C j ≤ i.1.2.2

open Classical in
/-- MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|r_i;p_ij=1|Σw_iC_i` as a decision problem over
bitstrings. -/
noncomputable def multiPurposeUnitJobShopReleaseWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiPurposeUnitJobShopReleaseWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ MultiPurposeUnitJobShopReleaseWeightedCompletionFeasible i)
  | none => false

/-- **MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|r_i;p_ij=1|Σw_iC_i` is NP-complete.** Source:
Timkovsky (1998); Brucker and Knust, scheduling classification, class `mpm_shop`. -/
public theorem_wanted multiPurposeUnitJobShopReleaseWeightedCompletion_npComplete :
    multiPurposeUnitJobShopReleaseWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiPurposeUnitJobShopReleaseWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopReleaseWeightedCompletion
