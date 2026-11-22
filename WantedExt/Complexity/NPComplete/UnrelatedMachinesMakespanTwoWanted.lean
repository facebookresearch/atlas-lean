/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNRELATED PARALLEL MACHINES WITH MAKESPAN 2 is NP-complete

Source:
J. K. Lenstra, D. B. Shmoys and É. Tardos, "Approximation algorithms for scheduling unrelated
parallel machines", Mathematical Programming 46 (1990), 259-271, doi:10.1007/BF01585745,
Theorem 5 ("For the minimum makespan problem on unrelated parallel machines, the question of
deciding if there exists a schedule with makespan at most 2 is NP-complete"; read in the CWI
report OS-R8714, 1987, of the same title);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING (the identical
machine version).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnrelatedMachinesMakespanTwo

/-!
# UNRELATED PARALLEL MACHINES WITH MAKESPAN 2 is NP-complete

INSTANCE: `n` independent jobs, `m` parallel machines, and for each job `j` and machine `i` a
processing time `p_ij`, a positive integer (the time job `j` needs when it is scheduled on
machine `i`). QUESTION: is there a schedule with makespan at most `2`, i.e. an assignment of
every job to one machine such that, for every machine `i`, the sum of `p_ij` over the jobs `j`
assigned to `i` is at most `2`?

This is `R || C_max` (Graham, Lawler, Lenstra and Rinnooy Kan) with the makespan bound fixed to
`2`. Jobs run without preemption, and the total time used by machine `i` is the sum of the
`p_ij` of its jobs, so a schedule is the assignment alone. The instance lists, for each job, its
`m` processing times (job `j` is the `j`-th row, machine `i` the `i`-th entry). Only whether
`p_ij` is `1`, `2` or larger matters, and Lenstra, Shmoys and Tardos's reduction from
3-DIMENSIONAL MATCHING uses only the times `1`, `2` and `3`, so the problem is NP-complete in the
strong sense; the times are written in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of machines, and for each job the list of its processing times
`p_1j, …, p_mj` on the `m` machines. -/
abbrev UnrelatedMachinesMakespanTwoInstance := ℕ × List (List ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed rows. -/
abbrev Job (i : UnrelatedMachinesMakespanTwoInstance) : Type := Fin i.2.length

/-- The machines of the instance, `Fin m`. -/
abbrev Machine (i : UnrelatedMachinesMakespanTwoInstance) : Type := Fin i.1

/-- The processing time `p_ij` of job `j` on machine `k`: entry `k` of row `j`. -/
def processingTime (i : UnrelatedMachinesMakespanTwoInstance) (j : Job i) (k : Machine i) : ℕ :=
  (i.2.get j).getD k 0

/-- Well-formedness of an instance: `m` is positive, every job lists one processing time per
machine, and every processing time is a positive integer. -/
def WellFormed (i : UnrelatedMachinesMakespanTwoInstance) : Prop :=
  0 < i.1 ∧ ∀ row ∈ i.2, row.length = i.1 ∧ ∀ p ∈ row, 0 < p

/-- Some assignment of the jobs to machines gives every machine total processing time at most
`2`. -/
def UnrelatedMachinesMakespanTwoFeasible (i : UnrelatedMachinesMakespanTwoInstance) : Prop :=
  ∃ σ : Job i → Machine i, ∀ k : Machine i,
    ∑ j ∈ Finset.univ.filter (fun j => σ j = k), processingTime i j k ≤ 2

open Classical in
/-- UNRELATED PARALLEL MACHINES WITH MAKESPAN 2 as a decision problem over bitstrings. -/
noncomputable def unrelatedMachinesMakespanTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnrelatedMachinesMakespanTwoInstance) x with
  | some i => decide (WellFormed i ∧ UnrelatedMachinesMakespanTwoFeasible i)
  | none => false

/-- **UNRELATED PARALLEL MACHINES WITH MAKESPAN 2 is NP-complete.** Source: Lenstra, Shmoys and
Tardos (1990), Theorem 5; Garey and Johnson (1979), [SS8] (identical machines). -/
public theorem_wanted unrelatedMachinesMakespanTwo_npComplete :
    unrelatedMachinesMakespanTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unrelatedMachinesMakespanTwoDec

end MetaMathlibExt.Complexity.NPComplete.UnrelatedMachinesMakespanTwo
