/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM PARALLEL MACHINES `PMPM|intree; p_i = 1; r_i|C_max`: definitions

Source:
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2(3)
(1977), 275-284, doi:10.1287/moor.2.3.275;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `mpm` (multi-purpose machine
problems), entry `PMPM|intree; p_i = 1; r_i|C_max` (minimal NP-hard in the strong sense, citing
Brucker, Garey and Johnson 1977);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 10 (multi-purpose machines).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ParallelMachinesInTreeReleaseMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesInTreeReleaseMakespan

open PrecedenceConstrainedScheduling (Task taskLength Prec)
open ParallelMachinesInTreeReleaseMakespan (ParallelMachinesInTreeReleaseMakespanInstance
  releaseDate)

/-- An instance: a `P|intree; r_i; p_i = 1|C_max` instance and the eligible machine sets, job `t`
having the `t`-th listed set `μ_t`. -/
abbrev MultipurposeParallelMachinesInTreeReleaseMakespanInstance :=
  ParallelMachinesInTreeReleaseMakespanInstance × List (List ℕ)

/-- The eligible machine set `μ_t` of job `t`. -/
def eligible (i : MultipurposeParallelMachinesInTreeReleaseMakespanInstance) (t : Task i.1.1) :
    List ℕ :=
  i.2.getD t []

/-- Well-formedness of an instance: a well-formed `P|intree; r_i; p_i = 1|C_max` instance, one
eligible set per job, and every eligible set nonempty with machines below `m`. -/
def WellFormed (i : MultipurposeParallelMachinesInTreeReleaseMakespanInstance) : Prop :=
  ParallelMachinesInTreeReleaseMakespan.WellFormed i.1 ∧ i.2.length = i.1.1.1.length ∧
    ∀ μ ∈ i.2, μ ≠ [] ∧ ∀ k ∈ μ, k < i.1.1.2.1

/-- Some schedule processes every job on an eligible machine, no two jobs on one machine at the
same time, respects the release dates and the precedence constraints, and has makespan at most
`K`. -/
def MultipurposeParallelMachinesInTreeReleaseMakespanFeasible
    (i : MultipurposeParallelMachinesInTreeReleaseMakespanInstance) : Prop :=
  ∃ σ : Task i.1.1 → ℕ, ∃ a : Task i.1.1 → ℕ, (∀ t, a t ∈ eligible i t) ∧
    (∀ t t', t ≠ t' → a t = a t' →
      σ t + taskLength i.1.1 t ≤ σ t' ∨ σ t' + taskLength i.1.1 t' ≤ σ t) ∧
    (∀ t, releaseDate i.1 t ≤ σ t) ∧
    (∀ t t', Prec i.1.1 t t' → σ t + taskLength i.1.1 t ≤ σ t') ∧
    ∀ t, σ t + taskLength i.1.1 t ≤ i.1.1.2.2.2

open Classical in
/-- `PMPM|intree; p_i = 1; r_i|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelMachinesInTreeReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelMachinesInTreeReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelMachinesInTreeReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesInTreeReleaseMakespan
