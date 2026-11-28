/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEADLOCK POTENTIAL: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4(3)
(1983), 286-300, doi:10.1016/0196-6774(83)90028-7, problem DEADLOCK POTENTIAL;
T. Minoura, "Deadlock avoidance revisited", Journal of the ACM 29(4) (1982), 1023-1048,
doi:10.1145/322344.322351.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeadlockPotential

/-- An instance: resource bounds `[B₁, …, B_m]`, the processes (each a list of steps, each step
a list of `m` integers as `(positive part, negative part)` pairs), and the partial schedule `S`
(a list of process indices). -/
abbrev DeadlockPotentialInstance := List ℕ × List (List (List (ℕ × ℕ))) × List ℕ

/-- The number `m` of resources. -/
def numResources (i : DeadlockPotentialInstance) : ℕ := i.1.length

/-- The number of processes. -/
def numProcesses (i : DeadlockPotentialInstance) : ℕ := i.2.1.length

/-- The bound `B_j` of resource `j`. -/
def bound (i : DeadlockPotentialInstance) (j : ℕ) : ℤ := (i.1.getD j 0 : ℤ)

/-- The number of steps of process `p`. -/
def procLength (i : DeadlockPotentialInstance) (p : ℕ) : ℕ := (i.2.1.getD p []).length

/-- The entry `a_j(v)` of the allocation vector of step `k` of process `p`. -/
def alloc (i : DeadlockPotentialInstance) (p k j : ℕ) : ℤ :=
  let e := ((i.2.1.getD p []).getD k []).getD j (0, 0)
  (e.1 : ℤ) - e.2

/-- `Σ_{t' < t} a_j(u_{t'})` for the partial schedule `σ`: the amount of resource `j` held after
its first `t` steps, where position `t'` is step `(σ.take t').count σ[t']` of process `σ[t']`. -/
def usage (i : DeadlockPotentialInstance) (σ : List ℕ) (t j : ℕ) : ℤ :=
  ∑ t' ∈ Finset.range t, alloc i (σ.getD t' 0) ((σ.take t').count (σ.getD t' 0)) j

/-- `σ` is a legal partial schedule: it names only processes, takes a prefix of each process
(at most its number of steps), and `0 ≤ Σ_{i ≤ t} a_j(u_i) ≤ B_j` for every resource `j` and
every `t` with `1 ≤ t ≤ |σ|`. -/
def IsLegal (i : DeadlockPotentialInstance) (σ : List ℕ) : Prop :=
  (∀ p ∈ σ, p < numProcesses i) ∧ (∀ p < numProcesses i, σ.count p ≤ procLength i p) ∧
    ∀ t ∈ Finset.Icc 1 σ.length, ∀ j < numResources i,
      0 ≤ usage i σ t j ∧ usage i σ t j ≤ bound i j

/-- `σ` is a deadlocked schedule: it is legal, (a) some process is not entirely contained in it,
and (b) for each such process `p`, its first step not in `σ` (step `σ.count p`) would exceed the
bound of some resource `j`. -/
def IsDeadlocked (i : DeadlockPotentialInstance) (σ : List ℕ) : Prop :=
  IsLegal i σ ∧ (∃ p < numProcesses i, σ.count p < procLength i p) ∧
    ∀ p < numProcesses i, σ.count p < procLength i p →
      ∃ j < numResources i, bound i j < alloc i p (σ.count p) j + usage i σ σ.length j

/-- Well-formedness of an instance: every step has an allocation vector of length `m`, every
process is legal (the schedule consisting of that process alone is legal), and `S` is a legal
partial schedule. -/
def WellFormed (i : DeadlockPotentialInstance) : Prop :=
  (∀ proc ∈ i.2.1, ∀ v ∈ proc, v.length = numResources i) ∧
    (∀ p < numProcesses i, IsLegal i (List.replicate (procLength i p) p)) ∧ IsLegal i i.2.2

/-- The partial schedule `S` can be extended to a deadlocked schedule `S ++ T`. -/
def DeadlockPotentialFeasible (i : DeadlockPotentialInstance) : Prop :=
  ∃ T : List ℕ, IsDeadlocked i (i.2.2 ++ T)

open Classical in
/-- DEADLOCK POTENTIAL as a decision problem over bitstrings. -/
noncomputable def deadlockPotentialDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := DeadlockPotentialInstance) x with
  | some i => decide (WellFormed i ∧ DeadlockPotentialFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DeadlockPotential
