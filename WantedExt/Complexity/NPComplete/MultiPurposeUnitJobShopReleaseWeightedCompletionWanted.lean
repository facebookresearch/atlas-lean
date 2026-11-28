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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiPurposeUnitJobShopReleaseWeightedCompletionDefs

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
`MultiPurposeJobShopThreeJobsDefs` (instance, operations, eligible machine sets, schedules and
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

/-- **MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|r_i;p_ij=1|Σw_iC_i` is NP-complete.** Source:
Timkovsky (1998); Brucker and Knust, scheduling classification, class `mpm_shop`. -/
public theorem_wanted multiPurposeUnitJobShopReleaseWeightedCompletion_npComplete :
    multiPurposeUnitJobShopReleaseWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiPurposeUnitJobShopReleaseWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopReleaseWeightedCompletion
