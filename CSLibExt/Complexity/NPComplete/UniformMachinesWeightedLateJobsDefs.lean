/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFORM PARALLEL MACHINE SCHEDULING, weighted number of late jobs (`Qm||Σw_iU_i`) is: definitions
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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UniformMachinesReleaseMakespanDefs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniformMachinesWeightedLateJobs

open MetaMathlibExt.Complexity.NPComplete.MultiprocessorScheduling (Task)
open MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactors
  (toMultiprocessorScheduling)
open MetaMathlibExt.Complexity.NPComplete.UniformMachinesReleaseMakespan
  (UniformMachinesReleaseMakespanInstance completion IsNonOverlapping)

/-- An instance: a `UniformMachinesReleaseMakespan` instance read as the processing times
`p_i`, the speeds (the `k`-th entry `(a, b)` is `s_k = a / b`), the bound `K` and the due dates
`d_i`, one per job; and the weights `w_i`, one per job. -/
abbrev UniformMachinesWeightedLateJobsInstance :=
  UniformMachinesReleaseMakespanInstance × List ℕ

/-- The due date `d_t` of job `t` (the `t`-th entry of the due-date list). -/
def dueDate (i : UniformMachinesWeightedLateJobsInstance)
    (t : Task (toMultiprocessorScheduling i.1.1)) : ℕ :=
  i.1.2.getD t 0

/-- The weight `w_t` of job `t` (the `t`-th entry of the weight list). -/
def weight (i : UniformMachinesWeightedLateJobsInstance)
    (t : Task (toMultiprocessorScheduling i.1.1)) : ℕ :=
  i.2.getD t 0

/-- Well-formedness of an instance for the fixed number `m` of machines: the
`UniformMachinesReleaseMakespan` conditions (positive processing times, exactly `m` positive
speeds, one due date per job), one weight per job, and positive due dates, weights and `K`. -/
def WellFormed (m : ℕ) (i : UniformMachinesWeightedLateJobsInstance) : Prop :=
  UniformMachinesReleaseMakespan.WellFormed m i.1 ∧ i.2.length = i.1.1.1.length ∧
    (∀ d ∈ i.1.2, 0 < d) ∧ (∀ w ∈ i.2, 0 < w) ∧ 0 < i.1.1.2.2

/-- Some schedule, a machine `μ(t)` and a start time `S(t) ≥ 0` for each job `t`, where jobs on
the same machine do not overlap, has total weight of late jobs (those with `C_t > d_t`) at
most `K`. -/
def UniformMachinesWeightedLateJobsFeasible (i : UniformMachinesWeightedLateJobsInstance) :
    Prop :=
  ∃ μ : Task (toMultiprocessorScheduling i.1.1) → Fin i.1.1.2.1.length,
    ∃ S : Task (toMultiprocessorScheduling i.1.1) → ℚ,
      IsNonOverlapping i.1.1 μ S ∧ (∀ t, 0 ≤ S t) ∧
        ∑ t ∈ Finset.univ.filter (fun t => (dueDate i t : ℚ) < completion i.1.1 μ S t),
          weight i t ≤ i.1.1.2.2

open Classical in
/-- UNIFORM PARALLEL MACHINE SCHEDULING on `m` machines, weighted number of late jobs
(`Qm||Σw_iU_i`), as a decision problem over bitstrings. -/
noncomputable def uniformMachinesWeightedLateJobsDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UniformMachinesWeightedLateJobsInstance) x with
  | some i => decide (WellFormed m i ∧ UniformMachinesWeightedLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UniformMachinesWeightedLateJobs
