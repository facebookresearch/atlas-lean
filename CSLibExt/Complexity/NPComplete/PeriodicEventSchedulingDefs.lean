/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERIODIC EVENT SCHEDULING (PESP): definitions

Source:
P. Serafini and W. Ukovich, "A mathematical model for periodic scheduling problems", SIAM Journal
on Discrete Mathematics 2 (1989), 550-581, doi:10.1137/0402049.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Int.ModEq

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PeriodicEventScheduling

/-- An instance: the number `n` of events, the period `T`, and the activities, activity `a`
given as `(i, j, ℓ_a, u_a)` with `ℓ_a` and `u_a` as pairs `(positive part, negative part)`. -/
abbrev PeriodicEventSchedulingInstance := ℕ × ℕ × List (ℕ × ℕ × (ℕ × ℕ) × (ℕ × ℕ))

/-- Well-formedness of an instance: the period is positive and every activity joins two
different events. -/
def WellFormed (i : PeriodicEventSchedulingInstance) : Prop :=
  0 < i.2.1 ∧ ∀ a ∈ i.2.2, a.1 < i.1 ∧ a.2.1 < i.1 ∧ a.1 ≠ a.2.1

/-- There is a periodic timetable: event times `π v < T` such that every activity
`(i, j, ℓ, u)` has a tension `x` with `ℓ ≤ x ≤ u` and `x ≡ π j - π i (mod T)`. -/
def PeriodicEventSchedulingFeasible (i : PeriodicEventSchedulingInstance) : Prop :=
  ∃ π : ℕ → ℕ, (∀ v < i.1, π v < i.2.1) ∧
    ∀ a ∈ i.2.2, ∃ x : ℤ,
      (a.2.2.1.1 : ℤ) - a.2.2.1.2 ≤ x ∧ x ≤ (a.2.2.2.1 : ℤ) - a.2.2.2.2 ∧
        x ≡ (π a.2.1 : ℤ) - π a.1 [ZMOD i.2.1]

open Classical in
/-- PERIODIC EVENT SCHEDULING as a decision problem over bitstrings. -/
noncomputable def periodicEventSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PeriodicEventSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PeriodicEventSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PeriodicEventScheduling
