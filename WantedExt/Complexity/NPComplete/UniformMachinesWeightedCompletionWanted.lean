/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFORM PARALLEL MACHINE SCHEDULING, total weighted completion time (`Qm||Σw_iC_i`) is
NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems without preemption" (`Qm||Σw_iC_i` maximal pseudopolynomially
solvable, citing Lawler, Lenstra, Rinnooy Kan and Shmoys (1989); `P2||Σw_iC_i` minimal NP-hard,
citing Bruno et al. (1974));
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling problems",
Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X,
Theorem 3(b) (PARTITION reduces to `P2||Σw_iC_i`);
J. Bruno, E. G. Coffman, Jr. and R. Sethi, "Scheduling independent tasks to reduce mean
finishing time", Communications of the ACM 17 (1974), 382-387, doi:10.1145/361011.361064;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE WEIGHTED
COMPLETION TIME (comment: remains NP-complete for `m = 2`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 1 (notation).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UniformMachinesWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniformMachinesWeightedCompletion

open MetaMathlibExt.Complexity.NPComplete.MultiprocessorScheduling (Task)
open MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactors
  (MultiprocessorSchedulingSpeedFactorsInstance toMultiprocessorScheduling)
open MetaMathlibExt.Complexity.NPComplete.UniformMachinesReleaseMakespan
  (completion IsNonOverlapping)

/-!
# UNIFORM PARALLEL MACHINE SCHEDULING, total weighted completion time, is NP-complete

For a fixed number `m ≥ 2` of machines (`m` is not part of the instance): INSTANCE: `m` uniform
parallel machines `M_1, …, M_m` with positive rational speeds `s_1, …, s_m`, each processing at
most one job at a time; jobs `1, …, n`, job `i` with a processing time `p_i ∈ ℤ⁺` and a weight
`w_i ∈ ℤ⁺`; and a positive integer bound `K`. Job `i` is processed without interruption on one
machine `M_k`, which takes `p_i / s_k` time units. QUESTION: is there a feasible schedule whose
total weighted completion time `Σ_i w_i C_i` is at most `K`, where `C_i` is the completion time
of job `i`?

This is `Qm||Σw_iC_i` in the notation of Brucker's *Scheduling Algorithms* and of the
Brucker-Knust classification. A schedule gives each job `i` a machine `μ(i)` and a start time
`S(i) ≥ 0`; then `C_i = S(i) + p_i / s_{μ(i)}`, and two different jobs on the same machine
occupy disjoint intervals `[S(i), C_i)`. The schedule model (`completion`, `IsNonOverlapping`)
and the well-formedness conditions are those of `UniformMachinesReleaseMakespanWanted`
(`Qm|r_i|C_max`), with the weights in place of the release dates; weights and `K` are
positive, as in Garey and Johnson's [SS13]. NP membership: a certificate is the machine of each
job and the job order on each machine; running the jobs of each machine back to back from time
`0` in that order gives start times that are sums of processing times, of size polynomial in the
input. NP-hardness: with `m = 2` and both speeds `1` this is
`P2||Σw_iC_i`, to which Lenstra, Rinnooy Kan and Brucker (1977, Theorem 3(b)) reduce PARTITION
(processing times and weights positive); for `m ≥ 3`, giving the other `m - 2` machines speed
`1 / (K + 1)` keeps that reduction correct, since a job of positive processing time and weight
on one of them completes after time `K` and alone contributes more than `K`. Binary encoding of
all numbers: for fixed `m` the problem is solvable in pseudo-polynomial time (Lawler et al.),
so it is not NP-complete in the strong sense unless P = NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNIFORM PARALLEL MACHINE SCHEDULING, total weighted completion time (`Qm||Σw_iC_i`), is
NP-complete for every fixed number `m ≥ 2` of machines.** Source: Brucker and Knust, class
"Parallel machine problems without preemption"; Lenstra, Rinnooy Kan and Brucker (1977),
Theorem 3(b); Bruno, Coffman and Sethi (1974); Garey and Johnson (1979), [SS13]. -/
public theorem_wanted uniformMachinesWeightedCompletion_npComplete (m : ℕ) (hm : 2 ≤ m) :
    uniformMachinesWeightedCompletionDec m ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (uniformMachinesWeightedCompletionDec m)

end MetaMathlibExt.Complexity.NPComplete.UniformMachinesWeightedCompletion
