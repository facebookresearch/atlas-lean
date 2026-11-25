/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED EARLINESS-TARDINESS ABOUT A COMMON DUE DATE is NP-complete

Source:
N. G. Hall and M. E. Posner, "Earliness-tardiness scheduling problems, I: weighted deviation of
completion times about a common due date", Operations Research 39 (1991), 836-846,
doi:10.1287/opre.39.5.836.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedEarlinessTardinessCommonDueDate

/-!
# WEIGHTED EARLINESS-TARDINESS ABOUT A COMMON DUE DATE is NP-complete

INSTANCE: a single machine; jobs `1, …, n` with processing times `p_j ∈ ℤ⁺` and weights
`w_j ∈ ℤ₀⁺`; a common due date `d` with `d ≥ ∑_j p_j` (the due date is unrestrictive: it is not
early enough to constrain the schedule); and a bound `K`.
QUESTION: is there a nonpreemptive schedule of the jobs on the machine whose total weighted
deviation `∑_j w_j |C_j - d|` of the completion times `C_j` from `d` is at most `K`?

In the three-field notation this is `1|d_j = d|∑ w_j |C_j - d|` with `d ≥ ∑_j p_j`. Hall and
Posner prove that its recognition version is NP-complete in the ordinary sense, and give a
pseudopolynomial dynamic program, so the binary encoding of the numbers matters. A schedule
assigns each job a start time `S_j ∈ ℤ₀⁺` (time starts at `0`; idle time is allowed); the
machine processes one job at a time, so the intervals `[S_j, S_j + p_j)` of distinct jobs are
disjoint, and `C_j = S_j + p_j`. The weighted deviation is written with `Int.natAbs`. The bound
`K` is a natural number (the objective is nonnegative).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs, job `j` given as `(p_j, w_j)` (processing time and weight), the
common due date `d` and the bound `K`. -/
abbrev WeightedEarlinessTardinessCommonDueDateInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: every processing time is positive and the due date is at
least the total processing time. -/
def WellFormed (i : WeightedEarlinessTardinessCommonDueDateInstance) : Prop :=
  (∀ job ∈ i.1, 0 < job.1) ∧ (i.1.map Prod.fst).sum ≤ i.2.1

/-- There is a nonpreemptive one-machine schedule with total weighted deviation at most `K`:
start times `S` such that distinct jobs occupy disjoint intervals `[S_j, S_j + p_j)`, and
`∑_j w_j |S_j + p_j - d| ≤ K`. -/
def WeightedEarlinessTardinessCommonDueDateFeasible
    (i : WeightedEarlinessTardinessCommonDueDateInstance) : Prop :=
  ∃ S : Fin i.1.length → ℕ,
    (∀ j k, j ≠ k → S j + (i.1.get j).1 ≤ S k ∨ S k + (i.1.get k).1 ≤ S j) ∧
    ∑ j, (i.1.get j).2 * (((S j + (i.1.get j).1 : ℕ) : ℤ) - i.2.1).natAbs ≤ i.2.2

open Classical in
/-- WEIGHTED EARLINESS-TARDINESS ABOUT A COMMON DUE DATE as a decision problem over bitstrings. -/
noncomputable def weightedEarlinessTardinessCommonDueDateDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedEarlinessTardinessCommonDueDateInstance) x with
  | some i => decide (WellFormed i ∧ WeightedEarlinessTardinessCommonDueDateFeasible i)
  | none => false

/-- **WEIGHTED EARLINESS-TARDINESS ABOUT A COMMON DUE DATE is NP-complete.** Source: Hall and
Posner (1991). -/
public theorem_wanted weightedEarlinessTardinessCommonDueDate_npComplete :
    weightedEarlinessTardinessCommonDueDateDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedEarlinessTardinessCommonDueDateDec

end MetaMathlibExt.Complexity.NPComplete.WeightedEarlinessTardinessCommonDueDate
