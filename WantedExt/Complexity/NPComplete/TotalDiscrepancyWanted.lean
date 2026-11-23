/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL DISCREPANCY is NP-complete

Source:
M. R. Garey, R. E. Tarjan, and G. T. Wilfong, "One-processor scheduling with symmetric
earliness and tardiness penalties", Mathematics of Operations Research 13 (1988), 330-348,
doi:10.1287/moor.13.2.330 (Section 2.1, the Total Discrepancy decision problem is
NP-complete); technical report version: "One-processor scheduling of tasks with preferred
starting times", Princeton University CS-TR-049-86 (1986).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalDiscrepancy

/-!
# TOTAL DISCREPANCY is NP-complete

INSTANCE (Garey, Tarjan, and Wilfong, Section 2.1): `N, k ∈ ℤ⁺` and, for `1 ≤ i ≤ N`, a task
length `lᵢ ∈ ℤ⁺` and a preferred midtime `Mᵢ ∈ ℤ⁺`. QUESTION: is there a schedule `S` such
that `cost(S) = ∑ᵢ |mᵢ(S) - Mᵢ| ≤ k`, where `mᵢ(S)` is the actual midtime of task `i` in `S`
(the time exactly half way between its starting and finishing times)?

A schedule assigns to each task `Tᵢ` a starting time `sᵢ` such that no two tasks overlap in
their execution: the execution intervals `[sᵢ, sᵢ + lᵢ]` and `[sⱼ, sⱼ + lⱼ]` of any two tasks
intersect only at their endpoints, so `mᵢ(S) = sᵢ + lᵢ / 2`. Starting times are real numbers
and are not bounded below. Since every length is positive, two intervals meet only at
endpoints exactly when one task finishes before the other starts. This is one-processor
scheduling with symmetric earliness and tardiness penalties, `1||∑|Cⱼ - dⱼ|`; the source
notes that preferred starting, completion and midpoint times are interchangeable. Binary
encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the tasks, task `i` being the `i`-th pair `(lᵢ, Mᵢ)` of length and preferred
midtime, and the bound `k`. -/
abbrev TotalDiscrepancyInstance := List (ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin N` for `N` listed pairs. -/
abbrev Task (i : TotalDiscrepancyInstance) : Type := Fin i.1.length

/-- The length `lᵢ` of task `t`. -/
def taskLength (i : TotalDiscrepancyInstance) (t : Task i) : ℕ :=
  (i.1.get t).1

/-- The preferred midtime `Mᵢ` of task `t`. -/
def preferredMidtime (i : TotalDiscrepancyInstance) (t : Task i) : ℕ :=
  (i.1.get t).2

/-- Starting times `s` form a one-processor schedule for positive lengths `l`: of any two
distinct tasks, one finishes before the other starts. -/
def IsSchedule {N : ℕ} (l : Fin N → ℕ) (s : Fin N → ℝ) : Prop :=
  ∀ a b, a ≠ b → s a + l a ≤ s b ∨ s b + l b ≤ s a

/-- Well-formedness of an instance: `N ∈ ℤ⁺` (some task), every length and preferred midtime
is positive, and `k ∈ ℤ⁺`. -/
def WellFormed (i : TotalDiscrepancyInstance) : Prop :=
  i.1 ≠ [] ∧ (∀ x ∈ i.1, 0 < x.1 ∧ 0 < x.2) ∧ 0 < i.2

/-- Some schedule has total discrepancy at most `k`: the sum over the tasks of the distance
between the actual midtime `sᵢ + lᵢ / 2` and the preferred midtime `Mᵢ` is at most `k`. -/
def TotalDiscrepancyFeasible (i : TotalDiscrepancyInstance) : Prop :=
  ∃ s : Task i → ℝ, IsSchedule (taskLength i) s ∧
    ∑ t, |s t + (taskLength i t : ℝ) / 2 - preferredMidtime i t| ≤ i.2

open Classical in
/-- TOTAL DISCREPANCY as a decision problem over bitstrings. -/
noncomputable def totalDiscrepancyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TotalDiscrepancyInstance) x with
  | some i => decide (WellFormed i ∧ TotalDiscrepancyFeasible i)
  | none => false

/-- **TOTAL DISCREPANCY is NP-complete.** Source: Garey, Tarjan, and Wilfong (1988),
Section 2.1. -/
public theorem_wanted totalDiscrepancy_npComplete :
    totalDiscrepancyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalDiscrepancyDec

end MetaMathlibExt.Complexity.NPComplete.TotalDiscrepancy
