/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TSP WITH RELEASE TIMES AND DEADLINES ON A LINE: definitions

Source:
J. N. Tsitsiklis, "Special cases of traveling salesman and repairman problems with time
windows", Networks 22(3) (1992), 263-282, doi:10.1002/net.3230220305, Theorem 2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TspReleaseDeadlinesOnLine

/-- An instance: the starting point `x*`, and the jobs as `(x_i, r_i, d_i)`. -/
abbrev TspReleaseDeadlinesOnLineInstance := ℕ × List (ℕ × ℕ × ℕ)

/-- The number of jobs. -/
abbrev numJobs (i : TspReleaseDeadlinesOnLineInstance) : ℕ := i.2.length

/-- The location `x_a` of job `a`. -/
def location (i : TspReleaseDeadlinesOnLineInstance) (a : ℕ) : ℕ := (i.2.getD a (0, 0, 0)).1

/-- The release time `r_a` of job `a`. -/
def release (i : TspReleaseDeadlinesOnLineInstance) (a : ℕ) : ℕ := (i.2.getD a (0, 0, 0)).2.1

/-- The deadline `d_a` of job `a`. -/
def deadline (i : TspReleaseDeadlinesOnLineInstance) (a : ℕ) : ℕ := (i.2.getD a (0, 0, 0)).2.2

/-- Well-formedness of an instance: there is at least one job. -/
def WellFormed (i : TspReleaseDeadlinesOnLineInstance) : Prop := 0 < numJobs i

/-- A feasible schedule exists: an order of the jobs and times `t` with every `t_a` in the
window of job `a`, the first job reachable from `x*` by its time, and each next job reachable
from the previous one in the time between them. -/
def TspReleaseDeadlinesOnLineFeasible (i : TspReleaseDeadlinesOnLineInstance) : Prop :=
  ∃ order : List ℕ, order.Perm (List.range (numJobs i)) ∧
    ∃ t : ℕ → ℕ, (∀ a < numJobs i, release i a ≤ t a ∧ t a ≤ deadline i a) ∧
      (∀ a ∈ order.head?, Nat.dist i.1 (location i a) ≤ t a) ∧
      ∀ p ∈ order.zip order.tail, t p.1 + Nat.dist (location i p.1) (location i p.2) ≤ t p.2

open Classical in
/-- TSP WITH RELEASE TIMES AND DEADLINES ON A LINE as a decision problem over bitstrings. -/
noncomputable def tspReleaseDeadlinesOnLineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TspReleaseDeadlinesOnLineInstance) x with
  | some i => decide (WellFormed i ∧ TspReleaseDeadlinesOnLineFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TspReleaseDeadlinesOnLine
