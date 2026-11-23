/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IDENTICAL PARALLEL MACHINE SCHEDULING, weighted number of late jobs (`Pm||Σw_iU_i`) is
NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS3] SEQUENCING TO MINIMIZE TARDY TASK WEIGHT
(the one-machine case, transformation from PARTITION credited to Karp (1972));
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multiprocessor task problems with parallel processors" (`Pm||Σw_iU_i` maximal
pseudopolynomially solvable, citing Lawler, Lenstra, Rinnooy Kan and Shmoys (1989));
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 1 (notation).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UniformMachinesWeightedLateJobsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelMachinesWeightedLateJobs

open MetaMathlibExt.Complexity.NPComplete.UniformMachinesWeightedLateJobs
  (UniformMachinesWeightedLateJobsInstance UniformMachinesWeightedLateJobsFeasible)

/-!
# IDENTICAL PARALLEL MACHINE SCHEDULING, weighted number of late jobs, is NP-complete

For a fixed number `m ≥ 1` of machines (`m` is not part of the instance): INSTANCE: `m`
identical parallel machines, each processing at most one job at a time; jobs `1, …, n`, job `i`
with a processing time `p_i ∈ ℤ⁺`, a due date `d_i ∈ ℤ⁺` and a weight `w_i ∈ ℤ⁺`; and a
positive integer bound `K`. Each job is processed without interruption on one machine.
QUESTION: is there a feasible schedule whose total weight `Σ_i w_i U_i` of late jobs is at most
`K`, where `U_i = 1` if `C_i > d_i` and `U_i = 0` otherwise, `C_i` being the completion time of
job `i`?

This is `Pm||Σw_iU_i` in the notation of Brucker's *Scheduling Algorithms* and of the
Brucker-Knust classification: the special case of `Qm||Σw_iU_i`
(`UniformMachinesWeightedLateJobsWanted`) in which every machine has speed `1`. An instance is a
`Qm||Σw_iU_i` instance whose `m` listed speeds are all `(1, 1)`, and the schedules and the
question are those of that module (a machine and a start time `S(i) ≥ 0` per job, jobs on one
machine occupying disjoint intervals `[S(i), S(i) + p_i)`); due dates, weights and `K` are
positive, as in Garey and Johnson's [SS3]. NP membership: a certificate is the machine of each
job and the job order on each machine; running the jobs of each machine back to back from time
`0` gives integer start times below the sum of the processing times. NP-hardness: with `m = 1`
this is SEQUENCING TO MINIMIZE TARDY TASK WEIGHT ([SS3], Karp 1972); for `m ≥ 2`, adding `m - 1`
jobs with processing time and due date `D + 1`, where `D` is the largest due date, and weight
`K + 1` keeps that problem's answer: in a schedule of late weight at most `K` each added job is
on time, so it starts at `0` and occupies its own machine up to time `D + 1`, and every on-time
original job runs on the remaining machine. Binary encoding of all numbers: for fixed `m` the
problem is solvable in pseudo-polynomial time (Lawler et al.), so it is not NP-complete in the
strong sense unless P = NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the fixed number `m` of machines: a well-formed
`Qm||Σw_iU_i` instance (positive processing times, due dates, weights and `K`; exactly `m`
speeds; one due date and one weight per job) in which every speed is `(1, 1)`, that is `1`. -/
def WellFormed (m : ℕ) (i : UniformMachinesWeightedLateJobsInstance) : Prop :=
  UniformMachinesWeightedLateJobs.WellFormed m i ∧ ∀ s ∈ i.1.1.2.1, s = (1, 1)

open Classical in
/-- IDENTICAL PARALLEL MACHINE SCHEDULING on `m` machines, weighted number of late jobs
(`Pm||Σw_iU_i`), as a decision problem over bitstrings. -/
noncomputable def parallelMachinesWeightedLateJobsDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UniformMachinesWeightedLateJobsInstance) x with
  | some i => decide (WellFormed m i ∧ UniformMachinesWeightedLateJobsFeasible i)
  | none => false

/-- **IDENTICAL PARALLEL MACHINE SCHEDULING, weighted number of late jobs (`Pm||Σw_iU_i`), is
NP-complete for every fixed number `m ≥ 1` of machines.** Source: Garey and Johnson (1979),
[SS3]; Karp (1972); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted parallelMachinesWeightedLateJobs_npComplete (m : ℕ) (hm : 1 ≤ m) :
    parallelMachinesWeightedLateJobsDec m ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (parallelMachinesWeightedLateJobsDec m)

end MetaMathlibExt.Complexity.NPComplete.ParallelMachinesWeightedLateJobs
