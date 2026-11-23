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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactorsWanted
public import Mathlib.Algebra.Order.Field.Rat

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

/-- An instance: the processing times `p_i` (job `i` is the `i`-th entry), the speeds (the
`k`-th entry `(a, b)` is `s_k = a / b`) and the bound `K`, as a
`MultiprocessorSchedulingSpeedFactors` instance; and the release dates `r_i`, one per job. -/
abbrev UniformMachinesReleaseMakespanInstance :=
  MultiprocessorSchedulingSpeedFactorsInstance × List ℕ

/-- The completion time `C_t = S(t) + p_t / s_{μ(t)}` of job `t` started at time `S(t)` on
machine `μ(t)`. -/
def completion (i : MultiprocessorSchedulingSpeedFactorsInstance)
    (μ : Task (toMultiprocessorScheduling i) → Fin i.2.1.length)
    (S : Task (toMultiprocessorScheduling i) → ℚ) (t : Task (toMultiprocessorScheduling i)) :
    ℚ :=
  S t + (taskLength (toMultiprocessorScheduling i) t : ℚ) / speed i (μ t)

/-- Each machine processes at most one job at a time: two different jobs on the same machine
occupy disjoint intervals `[S(t), C_t)`. -/
def IsNonOverlapping (i : MultiprocessorSchedulingSpeedFactorsInstance)
    (μ : Task (toMultiprocessorScheduling i) → Fin i.2.1.length)
    (S : Task (toMultiprocessorScheduling i) → ℚ) : Prop :=
  ∀ t u, t ≠ u → μ t = μ u → completion i μ S t ≤ S u ∨ completion i μ S u ≤ S t

/-- The release date `r_t` of job `t` (the `t`-th entry of the release-date list). -/
def release (i : UniformMachinesReleaseMakespanInstance)
    (t : Task (toMultiprocessorScheduling i.1)) : ℕ :=
  i.2.getD t 0

/-- Well-formedness of an instance for the fixed number `m` of machines: every processing time
is positive, exactly `m` speeds are listed, every speed `a / b` has `0 < a` and `0 < b`, and
there is one release date per job. -/
def WellFormed (m : ℕ) (i : UniformMachinesReleaseMakespanInstance) : Prop :=
  (∀ p ∈ i.1.1, 0 < p) ∧ i.1.2.1.length = m ∧ (∀ s ∈ i.1.2.1, 0 < s.1 ∧ 0 < s.2) ∧
    i.2.length = i.1.1.length

/-- Some schedule, a machine `μ(t)` and a start time `S(t)` for each job `t`, has makespan at
most `K`: jobs on the same machine do not overlap, and every job starts no earlier than its
release date and completes by `K`. -/
def UniformMachinesReleaseMakespanFeasible (i : UniformMachinesReleaseMakespanInstance) :
    Prop :=
  ∃ μ : Task (toMultiprocessorScheduling i.1) → Fin i.1.2.1.length,
    ∃ S : Task (toMultiprocessorScheduling i.1) → ℚ,
      IsNonOverlapping i.1 μ S ∧
        ∀ t, (release i t : ℚ) ≤ S t ∧ completion i.1 μ S t ≤ i.1.2.2

open Classical in
/-- UNIFORM PARALLEL MACHINE SCHEDULING with release dates on `m` machines (`Qm|r_i|C_max`) as
a decision problem over bitstrings. -/
noncomputable def uniformMachinesReleaseMakespanDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UniformMachinesReleaseMakespanInstance) x with
  | some i => decide (WellFormed m i ∧ UniformMachinesReleaseMakespanFeasible i)
  | none => false

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
