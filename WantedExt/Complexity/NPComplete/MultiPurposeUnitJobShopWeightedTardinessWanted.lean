/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|p_ij=1|Σw_iT_i is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
recorded in P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `JMPM2|p_ij=1|Σw_iT_i`, minimal NP-hard in the strong sense, Timkovsky (1998));
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM job shop
model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopWeightedTardiness

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule
  MPMWellFormed)

/-!
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|p_ij=1|Σw_iT_i is NP-complete

INSTANCE: `m = 2` machines `M₁, M₂`; jobs, each a chain of `n_j ≥ 1` unit-time operations
`O_{j1}, …, O_{jn_j}`, where each operation `O_{jk}` has a nonempty set `μ_{jk} ⊆ {M₁, M₂}` of
eligible machines and is processed on exactly one machine of `μ_{jk}`; for each job `j` a due date
`d_j ∈ ℤ₀⁺` and a weight `w_j ∈ ℤ₀⁺`; and a bound `K ∈ ℤ₀⁺`. Each machine processes at most one
operation at a time, and `O_{j,k+1}` cannot start before `O_{jk}` is completed. QUESTION: is there a
schedule whose total weighted tardiness `Σ_j w_j max(0, C_j - d_j)` is at most `K`, where `C_j` is
the completion time of job `j` (of its last operation)?

This is the job shop with multi-purpose machines (MPM) of Brucker (2004), Chapter 10, as stated in
`MultiPurposeJobShopThreeJobsWanted` (instance, operations, eligible machine sets, schedules and
`MPMWellFormed` are reused from there), with `m = 2` machines, every operation of length `1`, and
the total weighted tardiness criterion. Brucker and Knust's classification lists
`JMPM2|p_ij=1|Σw_iT_i` as minimal NP-hard in the strong sense, citing Timkovsky (1998), who reduces
scheduling problems on `m` identical parallel machines to `m`-machine unit-time job shops for a
class of criteria that includes the total weighted tardiness. The dedicated-machine job shop
`J2|p_ij=1|Σw_iT_i` is the special case in which every `μ_{jk}` is a single machine. The model puts
no condition on the machine sets of consecutive operations of a job.

The last component `K` of the reused instance is the bound on the total weighted tardiness; the
instance adds one pair `(d_j, w_j)` per job. Start times are natural numbers, which does not change
the answer (see `MultiPurposeJobShopThreeJobsWanted`). Operations are listed one by one, so the
instance size counts every operation (the cited hardness is in the strong sense). Binary encoding of
all numbers.

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
operations `(p_{jk}, μ_{jk})`, and the bound `K` on the total weighted tardiness) and one pair
`(d_j, w_j)` (due date, weight) per job. -/
abbrev MultiPurposeUnitJobShopWeightedTardinessInstance := MPMJobShopInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed MPM job shop instance with `m = 2` machines
(every job nonempty, every operation with a nonempty set of eligible machines in `{1, 2}`), every
operation of length `1`, and one pair `(d_j, w_j)` per job. -/
def WellFormed (i : MultiPurposeUnitJobShopWeightedTardinessInstance) : Prop :=
  MPMWellFormed 2 i.1 ∧ (∀ job ∈ i.1.2.1, ∀ o ∈ job, o.1 = 1) ∧ i.2.length = i.1.2.1.length

/-- Some MPM job shop schedule has `Σ_j w_j max(0, C_j - d_j) ≤ K` (natural subtraction
`C j - d_j` is `max(0, C_j - d_j)`), where `C j` is the completion time of the last operation of
job `j`. -/
def MultiPurposeUnitJobShopWeightedTardinessFeasible
    (i : MultiPurposeUnitJobShopWeightedTardinessInstance) : Prop :=
  ∃ a σ : Operation i.1 → ℕ, IsMPMJobShopSchedule i.1 a σ ∧
    ∃ C : Fin i.1.2.1.length → ℕ,
      (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
        C j = σ ⟨j, k⟩ + opLength i.1 ⟨j, k⟩) ∧
      ∑ j : Fin i.1.2.1.length, (i.2.getD j (0, 0)).2 * (C j - (i.2.getD j (0, 0)).1) ≤ i.1.2.2

open Classical in
/-- MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|p_ij=1|Σw_iT_i` as a decision problem over
bitstrings. -/
noncomputable def multiPurposeUnitJobShopWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiPurposeUnitJobShopWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ MultiPurposeUnitJobShopWeightedTardinessFeasible i)
  | none => false

/-- **MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|p_ij=1|Σw_iT_i` is NP-complete.** Source:
Timkovsky (1998); Brucker and Knust, scheduling classification, class `mpm_shop`. -/
public theorem_wanted multiPurposeUnitJobShopWeightedTardiness_npComplete :
    multiPurposeUnitJobShopWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiPurposeUnitJobShopWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopWeightedTardiness
