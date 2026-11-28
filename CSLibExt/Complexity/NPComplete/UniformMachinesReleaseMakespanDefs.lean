/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFORM PARALLEL MACHINE SCHEDULING with release dates (`Qm|r_i|C_max`): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactorsDefs
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniformMachinesReleaseMakespan

open MetaMathlibExt.Complexity.NPComplete.MultiprocessorScheduling (Task taskLength)
open MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactors
  (MultiprocessorSchedulingSpeedFactorsInstance toMultiprocessorScheduling speed)

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

end MetaMathlibExt.Complexity.NPComplete.UniformMachinesReleaseMakespan
