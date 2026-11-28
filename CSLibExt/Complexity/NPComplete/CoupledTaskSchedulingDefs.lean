/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COUPLED-TASK SCHEDULING: definitions

Source:
A. J. Orman and C. N. Potts, "On the complexity of coupled-task scheduling", Discrete Applied
Mathematics 72 (1997), 141-154, doi:10.1016/S0166-218X(96)00041-8.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoupledTaskScheduling

/-- An instance: the jobs as triples `(a_j, L_j, b_j)` (first operation length, exact delay,
second operation length) and the makespan bound `K`. -/
abbrev CoupledTaskSchedulingInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every operation length `a_j`, `b_j` is positive. -/
def WellFormed (i : CoupledTaskSchedulingInstance) : Prop :=
  ∀ t ∈ i.1, 0 < t.1 ∧ 0 < t.2.2

/-- The two operations of job `t = (a, L, b)` started at time `s`, as half-open time intervals
`[start, finish)`: the first operation occupies `[s, s + a)` and the second
`[s + a + L, s + a + L + b)`. -/
def operations (t : ℕ × ℕ × ℕ) (s : ℕ) : List (ℕ × ℕ) :=
  [(s, s + t.1), (s + t.1 + t.2.1, s + t.1 + t.2.1 + t.2.2)]

/-- There are start times `s j` such that every job completes by `K` and no two operations of
different jobs overlap on the machine. (The two operations of one job never overlap, since
`L_j ≥ 0`.) -/
def CoupledTaskSchedulingFeasible (i : CoupledTaskSchedulingInstance) : Prop :=
  ∃ s : Fin i.1.length → ℕ,
    (∀ j, s j + (i.1.get j).1 + (i.1.get j).2.1 + (i.1.get j).2.2 ≤ i.2) ∧
    ∀ j k, j ≠ k → ∀ I ∈ operations (i.1.get j) (s j), ∀ J ∈ operations (i.1.get k) (s k),
      I.2 ≤ J.1 ∨ J.2 ≤ I.1

open Classical in
/-- COUPLED-TASK SCHEDULING as a decision problem over bitstrings. -/
noncomputable def coupledTaskSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoupledTaskSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ CoupledTaskSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CoupledTaskScheduling
