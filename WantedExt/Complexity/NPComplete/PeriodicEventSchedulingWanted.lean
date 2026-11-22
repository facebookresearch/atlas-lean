/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERIODIC EVENT SCHEDULING (PESP) is NP-complete

Source:
P. Serafini and W. Ukovich, "A mathematical model for periodic scheduling problems", SIAM Journal
on Discrete Mathematics 2 (1989), 550-581, doi:10.1137/0402049.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Int.ModEq

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PeriodicEventScheduling

/-!
# PERIODIC EVENT SCHEDULING (PESP) is NP-complete

INSTANCE: a directed graph `G = (V, A)` with events `V = {0, …, n - 1}` and activities `A`, a
period `T ∈ ℤ⁺`, and for each activity `a = (i, j) ∈ A` a lower bound `ℓ_a ∈ ℤ` and an upper
bound `u_a ∈ ℤ`.
QUESTION: is there a periodic timetable, i.e. times `π_v ∈ {0, …, T - 1}` for the events, such
that every activity `a = (i, j)` has a periodic tension `x_a ∈ ℤ` with `ℓ_a ≤ x_a ≤ u_a` and
`x_a ≡ π_j - π_i (mod T)`?

This is the feasibility version of Serafini and Ukovich's periodic event scheduling problem,
which they show NP-complete. The congruence is Mathlib's `Int.ModEq`. Activities form a list,
so parallel activities between the same two events are allowed (as in timetabling instances);
an activity joins two different events. Lower and upper bounds are integers, each encoded as a
pair of naturals `(positive part, negative part)` representing their difference, as in
`ZeroOneILPWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PERIODIC EVENT SCHEDULING is NP-complete.** Source: Serafini and Ukovich (1989). -/
public theorem_wanted periodicEventScheduling_npComplete :
    periodicEventSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L periodicEventSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.PeriodicEventScheduling
