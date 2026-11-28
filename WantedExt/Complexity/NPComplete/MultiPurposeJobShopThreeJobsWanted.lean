/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|n=3|Cmax is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM job shop
model, and the statement that the MPM job shop problem with two machines and three jobs is
NP-hard, attributed to W. Meyer, *Geometrische Methoden zur Lösung von Job-Shop Problemen und
deren Verallgemeinerungen*, PhD thesis, Universität Osnabrück (1992));
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `JMPM2|n=3|C_max`, minimal NP-hard in the ordinary sense and maximal pseudopolynomially
solvable, citing B. Jurisch, Discrete Applied Mathematics 58 (1995), 145-156,
doi:10.1016/0166-218X(93)E0124-H, and Meyer (1992)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs

/-!
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|n=3|Cmax is NP-complete

INSTANCE: `m = 2` machines `M₁, M₂`; exactly `n = 3` jobs, each a chain of `n_j ≥ 1` operations
`O_{j1}, …, O_{jn_j}`, where each operation `O_{jk}` has a processing time `p_{jk} ∈ ℤ₀⁺` and a
nonempty set `μ_{jk} ⊆ {M₁, M₂}` of eligible machines and is processed on exactly one machine of
`μ_{jk}`; and a bound `K ∈ ℤ₀⁺`. Each machine processes at most one operation at a time, and
`O_{j,k+1}` cannot start before `O_{jk}` is completed. QUESTION: is there a schedule whose makespan,
the largest completion time of a job (of its last operation), is at most `K`?

This is the job shop with multi-purpose machines (MPM) of Brucker (2004), Chapter 10: in the
general shop with multi-purpose machines a machine set `μ_{ij}` is associated with each operation,
which is processed by one machine of that set, and the MPM job shop is the special case in which
the operations of each job form a chain. Brucker states that, contrary to the classical job shop
(where `J2|n=3|C_max` is polynomially solvable), the MPM job shop with two machines and three jobs
is NP-hard, citing Meyer (1992); Brucker and Knust's classification lists `JMPM2|n=3|C_max` as
minimal NP-hard in the ordinary sense and maximal pseudopolynomially solvable. The model puts no
condition on the machine sets of consecutive operations of a job: they may coincide, and two
consecutive operations, which never overlap in time, may use the same machine.

A schedule chooses a machine `a t ∈ μ_{jk}` and a start time `σ t ∈ ℤ₀⁺` for every operation `t`;
operation `t` occupies its machine during the half-open interval `[σ t, σ t + p_t)`, and two
different operations on the same machine do not overlap: if both have positive length, one ends
before the other starts; an operation of length `0` occupies no machine time. Start times are natural numbers: shifting every
operation of a feasible schedule as early as its machine and job predecessors allow makes every
start time `0` or the completion time of another operation, hence an integer, and completes no
operation later, so this does not change the answer. The number of machines is part of the
instance, and `WellFormed` fixes it to `2` and the number of jobs to `3`. Numbers use the binary
encoding (the problem is NP-hard in the ordinary sense only).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|n=3|C_max` is NP-complete.** Source: Brucker (2004),
Chapter 10 (Meyer (1992)); Brucker and Knust, scheduling classification, class `mpm_shop`. -/
public theorem_wanted multiPurposeJobShopThreeJobs_npComplete :
    multiPurposeJobShopThreeJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiPurposeJobShopThreeJobsDec

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs
