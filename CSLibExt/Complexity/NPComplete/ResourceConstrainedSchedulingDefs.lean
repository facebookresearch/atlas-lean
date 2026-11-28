/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS10] RESOURCE CONSTRAINED
SCHEDULING;
M. R. Garey and D. S. Johnson, "Complexity results for multiprocessor scheduling under resource
constraints", SIAM Journal on Computing 4 (1975), 397-411, doi:10.1137/0204035.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedScheduling

/-- An instance: the number of processors `m`, the number of resources `r`, the bounds
`B_0, …, B_{r-1}`, one row `(R_0(t), …, R_{r-1}(t))` per task `t`, and the deadline `D`. -/
abbrev ResourceConstrainedSchedulingInstance := ℕ × ℕ × List ℕ × List (List ℕ) × ℕ

/-- The tasks of the instance, `Fin n` for `n` rows of the requirement table. -/
abbrev Task (i : ResourceConstrainedSchedulingInstance) : Type := Fin i.2.2.2.1.length

/-- The requirement `R_k(t)` of task `t` for resource `k`. -/
def req (i : ResourceConstrainedSchedulingInstance) (t : Task i) (k : ℕ) : ℕ :=
  (i.2.2.2.1.getD t []).getD k 0

/-- The bound `B_k` of resource `k`. -/
def bound (i : ResourceConstrainedSchedulingInstance) (k : ℕ) : ℕ :=
  i.2.2.1.getD k 0

/-- `S(u)`: the tasks running at time `u` under `σ`, `σ(t) ≤ u < σ(t) + l(t)` with `l(t) = 1`. -/
def running (i : ResourceConstrainedSchedulingInstance) (σ : Task i → ℕ) (u : ℕ) :
    Finset (Task i) :=
  Finset.univ.filter fun t => σ t ≤ u ∧ u < σ t + 1

/-- Well-formedness of an instance: `0 < m`, `0 < r`, there are `r` bounds, each positive, every
task has `r` requirements with `R_k(t) ≤ B_k`, and `0 < D`. -/
def WellFormed (i : ResourceConstrainedSchedulingInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ i.2.2.1.length = i.2.1 ∧ (∀ b ∈ i.2.2.1, 0 < b) ∧
    (∀ row ∈ i.2.2.2.1, row.length = i.2.1 ∧ ∀ k < i.2.1, row.getD k 0 ≤ i.2.2.1.getD k 0) ∧
    0 < i.2.2.2.2

/-- Some `m`-processor schedule of the unit-length tasks meets the deadline and, at every time,
keeps the total requirement of the running tasks within each resource bound. -/
def ResourceConstrainedSchedulingFeasible (i : ResourceConstrainedSchedulingInstance) : Prop :=
  ∃ σ : Task i → ℕ, (∀ t, σ t + 1 ≤ i.2.2.2.2) ∧
    (∀ u, (running i σ u).card ≤ i.1) ∧
    ∀ u, ∀ k < i.2.1, ∑ t ∈ running i σ u, req i t k ≤ bound i k

open Classical in
/-- RESOURCE CONSTRAINED SCHEDULING as a decision problem over bitstrings. -/
noncomputable def resourceConstrainedSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ResourceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ ResourceConstrainedSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedScheduling
