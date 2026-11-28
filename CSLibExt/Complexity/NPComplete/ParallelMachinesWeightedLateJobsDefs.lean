/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IDENTICAL PARALLEL MACHINE SCHEDULING, weighted number of late jobs (`Pm||Σw_iU_i`) is: definitions
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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UniformMachinesWeightedLateJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelMachinesWeightedLateJobs

open MetaMathlibExt.Complexity.NPComplete.UniformMachinesWeightedLateJobs
  (UniformMachinesWeightedLateJobsInstance UniformMachinesWeightedLateJobsFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.ParallelMachinesWeightedLateJobs
