/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS AND UNIT TIMES, total tardiness: definitions
(`PMPM2|chains;p_i=1|ΣT_i`) is NP-complete

Source:
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with
precedence constraints", ORSA Journal on Computing 2 (1990), 346-352,
doi:10.1287/ijoc.2.4.346 (`1|chains, pⱼ = 1|∑ Tⱼ`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multi-purpose machine problems" (`PMPM2|chains; p_i=1|ΣT_i`, minimal NP-hard in the
strong sense, as a single-machine problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsTardiness

open MultiPurposeJobShopThreeJobs (Operation opLength IsMPMJobShopSchedule)
open UnitFlowShopPrecedenceMakespan (Prec)
open MultipurposeParallelTwoMachinesUnitChainsMakespan
  (MultipurposeParallelTwoMachinesUnitChainsMakespanInstance)

/-- An instance: a `PMPM2|chains; p_i=1|C_max` instance (the MPM job-shop instance, whose bound
component is `K`, and the precedence arcs) and the due dates, job `j` having the `j`-th listed
due date `d_j`. -/
abbrev MultipurposeParallelTwoMachinesUnitChainsTardinessInstance :=
  MultipurposeParallelTwoMachinesUnitChainsMakespanInstance × List ℕ

/-- The due date `d_j` of job `j`. -/
def dueDate (i : MultipurposeParallelTwoMachinesUnitChainsTardinessInstance)
    (j : Fin i.1.1.2.1.length) : ℕ :=
  i.2.getD j 0

/-- Well-formedness of an instance: a well-formed `PMPM2|chains; p_i=1|C_max` instance (two
machines, nonempty machine sets in `{1, 2}`, unit single-operation jobs, acyclic arcs naming jobs
that form chains) and one due date per job. -/
def WellFormed (i : MultipurposeParallelTwoMachinesUnitChainsTardinessInstance) : Prop :=
  MultipurposeParallelTwoMachinesUnitChainsMakespan.WellFormed i.1 ∧
    i.2.length = i.1.1.2.1.length

/-- Some MPM schedule of the jobs obeys the precedence arcs and has total tardiness at most `K`:
the sum, over the operations `t` (one per job), of `σ t + p_t - d_j` for the job `j` of `t`. -/
def MultipurposeParallelTwoMachinesUnitChainsTardinessFeasible
    (i : MultipurposeParallelTwoMachinesUnitChainsTardinessInstance) : Prop :=
  ∃ a σ : Operation i.1.1 → ℕ, IsMPMJobShopSchedule i.1.1 a σ ∧
    (∀ t t' : Operation i.1.1, Prec i.1.2 t.1 t'.1 → σ t + opLength i.1.1 t ≤ σ t') ∧
    (∑ t : Operation i.1.1, (σ t + opLength i.1.1 t - dueDate i t.1)) ≤ i.1.1.2.2

open Classical in
/-- `PMPM2|chains; p_i=1|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesUnitChainsTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesUnitChainsTardinessInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultipurposeParallelTwoMachinesUnitChainsTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsTardiness
