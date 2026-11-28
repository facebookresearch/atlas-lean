/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH RELEASE DATES, total completion time: definitions
(`PMPM2|rᵢ|ΣCᵢ`) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 10 (multi-purpose machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Parallel machine problems with
multi-purpose machines", which lists `PMPM2|r_i|ΣC_i` as minimal NP-hard in the strong sense
("Single-machine problem");
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling problems",
Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X (the
single-machine problem `1|r_j|ΣC_j`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesReleaseTotalCompletion

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength MPMWellFormed
  IsMPMJobShopSchedule)

/-- An instance: an MPM job-shop instance (machines, jobs as lists of operations `(pᵢ, μᵢ)`, the
bound `K`) and the release dates `rᵢ`, job `j` having the `j`-th listed release date. -/
abbrev MultipurposeParallelTwoMachinesReleaseTotalCompletionInstance := MPMJobShopInstance × List ℕ

/-- Well-formedness of an instance: a well-formed MPM job-shop instance with `m = 2` machines in
which every job has exactly one operation, and one release date per job. -/
def WellFormed (i : MultipurposeParallelTwoMachinesReleaseTotalCompletionInstance) : Prop :=
  MPMWellFormed 2 i.1 ∧ (∀ job ∈ i.1.2.1, job.length = 1) ∧ i.2.length = i.1.2.1.length

/-- Some MPM schedule of the jobs starts every job no earlier than its release date and has total
completion time `Σ (σ t + p_t)` at most `K`. -/
def MultipurposeParallelTwoMachinesReleaseTotalCompletionFeasible
    (i : MultipurposeParallelTwoMachinesReleaseTotalCompletionInstance) : Prop :=
  ∃ a σ : Operation i.1 → ℕ, IsMPMJobShopSchedule i.1 a σ ∧
    (∀ t, i.2.getD t.1 0 ≤ σ t) ∧ (∑ t, (σ t + opLength i.1 t)) ≤ i.1.2.2

open Classical in
/-- `PMPM2|rᵢ|ΣCᵢ` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesReleaseTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesReleaseTotalCompletionInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultipurposeParallelTwoMachinesReleaseTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesReleaseTotalCompletion
