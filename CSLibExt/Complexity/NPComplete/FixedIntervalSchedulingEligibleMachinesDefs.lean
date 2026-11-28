/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIXED-INTERVAL SCHEDULING ON ELIGIBLE MACHINES: definitions

Source:
E. M. Arkin and E. B. Silverberg, "Scheduling jobs with fixed start and end times", Discrete
Applied Mathematics 18 (1987), 1-8, doi:10.1016/0166-218X(87)90037-0;
D. Hermelin, Y. Itzhaki, H. Molter, and D. Shabtay, "Hardness of interval scheduling on
unrelated machines", arXiv:2206.12825 (2022), Sections 1-2 (problem definition, and the
statement that Arkin and Silverberg proved the problem strongly NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedIntervalSchedulingEligibleMachines

/-- A job: start time `s`, finish time `f`, weight `w`, and the list of its eligible machines. -/
abbrev Job := ℕ × ℕ × ℕ × List ℕ

/-- An instance: the number `m` of machines, the jobs in order, and the bound `W`. -/
abbrev FixedIntervalSchedulingEligibleMachinesInstance := ℕ × List Job × ℕ

/-- Well-formedness of an instance: every job has `s < f`, and every eligible machine index of
every job is below `m`. -/
def WellFormed (i : FixedIntervalSchedulingEligibleMachinesInstance) : Prop :=
  ∀ job ∈ i.2.1, job.1 < job.2.1 ∧ ∀ k ∈ job.2.2.2, k < i.1

/-- Two jobs conflict when their intervals intersect: each starts before the other finishes. -/
def Conflict (a b : Job) : Prop :=
  a.1 < b.2.1 ∧ b.1 < a.2.1

/-- Some schedule `σ` (job `j` goes to machine `σ j`, or is rejected when `σ j = none`) maps
every scheduled job to one of its eligible machines, maps no two distinct conflicting jobs to
the same machine, and schedules jobs of total weight at least `W`. -/
def FixedIntervalSchedulingEligibleMachinesFeasible
    (i : FixedIntervalSchedulingEligibleMachinesInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Option (Fin i.1),
    (∀ j : Fin i.2.1.length, ∀ k : Fin i.1, σ j = some k → (k : ℕ) ∈ (i.2.1.get j).2.2.2) ∧
    (∀ j j' : Fin i.2.1.length, j ≠ j' → ∀ k : Fin i.1, σ j = some k → σ j' = some k →
      ¬ Conflict (i.2.1.get j) (i.2.1.get j')) ∧
    i.2.2 ≤ ∑ j with (σ j).isSome, (i.2.1.get j).2.2.1

open Classical in
/-- FIXED-INTERVAL SCHEDULING ON ELIGIBLE MACHINES as a decision problem over bitstrings. -/
noncomputable def fixedIntervalSchedulingEligibleMachinesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FixedIntervalSchedulingEligibleMachinesInstance) x with
  | some i => decide (WellFormed i ∧ FixedIntervalSchedulingEligibleMachinesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FixedIntervalSchedulingEligibleMachines
