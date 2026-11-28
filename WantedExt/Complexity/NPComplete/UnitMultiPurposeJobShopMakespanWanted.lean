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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnitMultiPurposeJobShopMakespanDefs

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

/-- **MULTIPURPOSE-MACHINE JOB SHOP `JMPM3|p_ij=1|C_max` is NP-complete.** Source: Garey and
Johnson (1979), [SS18], comment; Lenstra and Rinnooy Kan (1979); Brucker and Knust,
scheduling classification, class `mpm_shop`. -/
public theorem_wanted unitMultiPurposeJobShopMakespan_npComplete :
    unitMultiPurposeJobShopMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitMultiPurposeJobShopMakespanDec

end MetaMathlibExt.Complexity.NPComplete.UnitMultiPurposeJobShopMakespan
