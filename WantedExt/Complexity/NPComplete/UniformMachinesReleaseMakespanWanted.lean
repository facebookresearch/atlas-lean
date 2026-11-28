/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFORM PARALLEL MACHINE SCHEDULING with release dates (`Qm|r_i|C_max`) is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems without preemption" (`Qm|r_i|C_max` maximal pseudopolynomially
solvable, citing Lawler, Lenstra, Rinnooy Kan and Shmoys (1989); `P2||C_max` minimal NP-hard,
citing Lenstra et al. (1977));
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling problems",
Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X,
Theorem 3(a) (PARTITION reduces to `P2||C_max`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING (comment:
remains NP-complete for `m = 2`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 1 (notation).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UniformMachinesReleaseMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniformMachinesReleaseMakespan

open MetaMathlibExt.Complexity.NPComplete.MultiprocessorScheduling (Task taskLength)
open MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactors
  (MultiprocessorSchedulingSpeedFactorsInstance toMultiprocessorScheduling speed)

/-!
# UNIFORM PARALLEL MACHINE SCHEDULING with release dates is NP-complete

For a fixed number `m ≥ 2` of machines (`m` is not part of the instance): INSTANCE: `m` uniform
parallel machines `M_1, …, M_m` with positive rational speeds `s_1, …, s_m`, each processing at
most one job at a time; jobs `1, …, n`, job `i` with a processing time `p_i ∈ ℤ⁺` and a release
date `r_i ∈ ℤ₀⁺`; and an integer bound `K`. Job `i` is processed without interruption on one
machine `M_k`, which takes `p_i / s_k` time units, and cannot start before `r_i`.
QUESTION: is there a feasible schedule whose makespan `max_i C_i` is at most `K`, where `C_i` is
the completion time of job `i`?

This is `Qm|r_i|C_max` in the notation of Brucker's *Scheduling Algorithms* and of the
Brucker-Knust classification. A schedule gives each job `i` a machine `μ(i)` and a start time
`S(i) ≥ r_i`; then `C_i = S(i) + p_i / s_{μ(i)}`, and two different jobs on the same machine
occupy disjoint intervals `[S(i), C_i)`. Start times are rational, since processing times
`p_i / s_k` are. NP membership: a certificate is the machine of each job and the job order on
each machine; starting each job as early as possible in that order gives start times that are
sums of release dates and processing times, of size polynomial in the input. NP-hardness: with
`m = 2`, both speeds `1` and all release dates `0` this is `P2||C_max`, to which Lenstra,
Rinnooy Kan and Brucker (1977, Theorem 3(a)) reduce PARTITION (all processing times positive);
for `m ≥ 3`, giving the other `m - 2` machines speed `1 / (K + 1)` keeps that reduction correct,
since a job of positive processing time on one of them completes after time `K`. Binary
encoding of all numbers: for fixed `m` the problem is solvable in pseudo-polynomial time (Lawler
et al.), so it is NP-complete only in the ordinary sense.

The processing times, the speeds and the bound `K` form a `MultiprocessorSchedulingSpeedFactors`
instance (whose speed `(a, b)` stands for `a / b`, and whose `m` is the number of listed speeds);
this module uses its job type, processing times and speeds, but not its well-formedness, which
normalizes the speeds (`s_1 = 1`, `s_k ≥ 1`); here a speed is any positive rational.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNIFORM PARALLEL MACHINE SCHEDULING with release dates (`Qm|r_i|C_max`) is NP-complete
for every fixed number `m ≥ 2` of machines.** Source: Brucker and Knust, class "Parallel
machine problems without preemption"; Lenstra, Rinnooy Kan and Brucker (1977), Theorem 3(a);
Garey and Johnson (1979), [SS8]. -/
public theorem_wanted uniformMachinesReleaseMakespan_npComplete (m : ℕ) (hm : 2 ≤ m) :
    uniformMachinesReleaseMakespanDec m ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (uniformMachinesReleaseMakespanDec m)

end MetaMathlibExt.Complexity.NPComplete.UniformMachinesReleaseMakespan
