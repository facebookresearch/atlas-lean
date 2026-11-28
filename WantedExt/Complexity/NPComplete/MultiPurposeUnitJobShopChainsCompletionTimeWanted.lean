/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|chains;p_ij=1|ΣC_i is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
recorded in P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `JMPM2|chains;p_ij=1|ΣC_i`, minimal NP-hard in the strong sense, Timkovsky (1998));
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM job shop
model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiPurposeUnitJobShopChainsCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopChainsCompletionTime

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule
  MPMWellFormed)

/-!
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|chains;p_ij=1|ΣC_i is NP-complete

INSTANCE: `m = 2` machines `M₁, M₂`; jobs, each a chain of `n_j ≥ 1` unit-time operations
`O_{j1}, …, O_{jn_j}`, where each operation `O_{jk}` has a nonempty set `μ_{jk} ⊆ {M₁, M₂}` of
eligible machines and is processed on exactly one machine of `μ_{jk}`; a precedence relation on the
jobs consisting of disjoint chains (each job has at most one immediate predecessor and at most one
immediate successor); and a bound `K ∈ ℤ₀⁺`. Each machine processes at most one operation at a
time, `O_{j,k+1}` cannot start before `O_{jk}` is completed, and if `j` precedes `j'`, no operation
of `j'` starts before `j` is completed. QUESTION: is there a schedule whose total completion time
`Σ_j C_j` is at most `K`, where `C_j` is the completion time of job `j` (of its last operation)?

This is the job shop with multi-purpose machines (MPM) of Brucker (2004), Chapter 10, as stated in
`MultiPurposeJobShopThreeJobsDefs` (instance, operations, eligible machine sets, schedules and
`MPMWellFormed` are reused from there), with `m = 2` machines, every operation of length `1`, chain
precedence constraints between jobs, and the total completion time criterion. Brucker and Knust's
classification lists `JMPM2|chains;p_ij=1|ΣC_i` as minimal NP-hard in the strong sense, citing
Timkovsky (1998), who reduces scheduling problems on `m` identical parallel machines to `m`-machine
unit-time job shops for a class of criteria that includes the total completion time. The
dedicated-machine job shop `J2|chains;p_ij=1|ΣC_i` is the special case in which every `μ_{jk}` is a
single machine. The model puts no condition on the machine sets of consecutive operations of a job.

The last component `K` of the reused instance is the bound on `Σ_j C_j`. The chains are given by
the list of their arcs `(j, j')`, `j` the immediate predecessor of `j'`. `WellFormed` requires every
arc to name two jobs, no two arcs with the same tail or the same head, and no cycle (the transitive
closure `Relation.TransGen` of the arc relation is irreflexive); the precedence relation is that
transitive closure. The constraint is imposed on the arcs; on the rest of the transitive closure it
follows, since every job starts its first operation before it completes its last. Start times are
natural numbers, which does not change the answer (see `MultiPurposeJobShopThreeJobsDefs`).
Operations are listed one by one, so the instance size counts every operation (the cited hardness
is in the strong sense). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|chains;p_ij=1|ΣC_i` is NP-complete.** Source:
Timkovsky (1998); Brucker and Knust, scheduling classification, class `mpm_shop`. -/
public theorem_wanted multiPurposeUnitJobShopChainsCompletionTime_npComplete :
    multiPurposeUnitJobShopChainsCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiPurposeUnitJobShopChainsCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopChainsCompletionTime
