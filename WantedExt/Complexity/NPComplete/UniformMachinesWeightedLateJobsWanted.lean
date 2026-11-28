/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFORM PARALLEL MACHINE SCHEDULING, weighted number of late jobs (`Qm||Σw_iU_i`) is
NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS3] SEQUENCING TO MINIMIZE TARDY TASK WEIGHT
(the one-machine case, transformation from PARTITION credited to Karp (1972));
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems without preemption" (`Qm||Σw_iU_i` maximal pseudopolynomially
solvable, citing Lawler, Lenstra, Rinnooy Kan and Shmoys (1989));
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 1 (notation).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UniformMachinesWeightedLateJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniformMachinesWeightedLateJobs

open MetaMathlibExt.Complexity.NPComplete.MultiprocessorScheduling (Task)
open MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactors
  (toMultiprocessorScheduling)
open MetaMathlibExt.Complexity.NPComplete.UniformMachinesReleaseMakespan
  (UniformMachinesReleaseMakespanInstance completion IsNonOverlapping)

/-!
# UNIFORM PARALLEL MACHINE SCHEDULING, weighted number of late jobs, is NP-complete

For a fixed number `m ≥ 1` of machines (`m` is not part of the instance): INSTANCE: `m` uniform
parallel machines `M_1, …, M_m` with positive rational speeds `s_1, …, s_m`, each processing at
most one job at a time; jobs `1, …, n`, job `i` with a processing time `p_i ∈ ℤ⁺`, a due date
`d_i ∈ ℤ⁺` and a weight `w_i ∈ ℤ⁺`; and a positive integer bound `K`. Job `i` is processed
without interruption on one machine `M_k`, which takes `p_i / s_k` time units. QUESTION: is
there a feasible schedule whose total weight `Σ_i w_i U_i` of late jobs is at most `K`, where
`U_i = 1` if `C_i > d_i` and `U_i = 0` otherwise, `C_i` being the completion time of job `i`?

This is `Qm||Σw_iU_i` in the notation of Brucker's *Scheduling Algorithms* and of the
Brucker-Knust classification. A schedule gives each job `i` a machine `μ(i)` and a start time
`S(i) ≥ 0`; then `C_i = S(i) + p_i / s_{μ(i)}`, and two different jobs on the same machine
occupy disjoint intervals `[S(i), C_i)`. The schedule model (`completion`, `IsNonOverlapping`)
and the base well-formedness are those of `UniformMachinesReleaseMakespanWanted`
(`Qm|r_i|C_max`), with the due dates in place of the release dates; due dates, weights and `K`
are positive, as in Garey and Johnson's [SS3]. NP membership: a certificate is the machine of
each job and the job order on each machine; running the jobs of each machine back to back from
time `0` in that order gives start times that are sums of processing times, of size polynomial
in the input. NP-hardness: with `m = 1` and speed `1` this is SEQUENCING TO MINIMIZE TARDY TASK
WEIGHT ([SS3], Karp 1972); for `m ≥ 2`, giving the other `m - 1` machines speed `1 / (D + 1)`,
where `D` is the largest due date, keeps that problem's answer, since a job placed on one of
them completes after time `D` and is late, and late jobs can as well run on `M_1` after the
others. Binary encoding of all numbers: for fixed `m` the problem is solvable in
pseudo-polynomial time (Lawler et al.), so it is not NP-complete in the strong sense unless
P = NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNIFORM PARALLEL MACHINE SCHEDULING, weighted number of late jobs (`Qm||Σw_iU_i`), is
NP-complete for every fixed number `m ≥ 1` of machines.** Source: Garey and Johnson (1979),
[SS3]; Karp (1972); Brucker and Knust, class "Parallel machine problems without preemption". -/
public theorem_wanted uniformMachinesWeightedLateJobs_npComplete (m : ℕ) (hm : 1 ≤ m) :
    uniformMachinesWeightedLateJobsDec m ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (uniformMachinesWeightedLateJobsDec m)

end MetaMathlibExt.Complexity.NPComplete.UniformMachinesWeightedLateJobs
