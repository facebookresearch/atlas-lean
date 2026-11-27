/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EARLINESS-TARDINESS WITH A RESTRICTIVE COMMON DUE DATE is NP-complete

Source:
N. G. Hall, W. Kubiak, and S. P. Sethi, "Earliness-tardiness scheduling problems, II:
deviation of completion times about a restrictive common due date", Operations Research 39
(1991), 847-856, doi:10.1287/opre.39.5.847 (the recognition version is NP-complete in the
ordinary sense);
J. A. Hoogeveen and S. L. van de Velde, "Scheduling around a small common due date",
European Journal of Operational Research 55 (1991), 237-242,
doi:10.1016/0377-2217(91)90228-N (Theorem 3, with all weights equal to 1; independent proof).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EarlinessTardinessRestrictiveCommonDueDate

/-!
# EARLINESS-TARDINESS WITH A RESTRICTIVE COMMON DUE DATE is NP-complete

INSTANCE (Hoogeveen and van de Velde): a set of `n` jobs to be scheduled on a single machine
that can handle only one job at a time and is continuously available from time `0` onwards,
job `Jᵢ` having a given positive integral uninterrupted processing time `pᵢ`; an integral
common due date `d` smaller than the sum of the processing times (`d < ∑ pᵢ`, the
restrictive case); and a nonnegative integer `y`. QUESTION: is there a schedule `S`, which
defines for each job `Jᵢ` a completion time `Cᵢ` such that the jobs do not overlap in their
execution, with `f(S) = ∑ᵢ |Cᵢ - d| ≤ y`?

This is `1|dⱼ = d|∑|Cⱼ - d|` (unit earliness and tardiness weights) with `d < ∑ pⱼ`, Hall,
Kubiak, and Sethi's problem. Job `Jᵢ` occupies `[Cᵢ - pᵢ, Cᵢ]`; it starts at or after time `0`,
and of any two distinct jobs one completes before the other starts. Completion times are real
numbers; idle time is allowed. Binary encoding of all numbers (the problem is NP-complete in
the ordinary sense and pseudopolynomially solvable).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the processing times `pᵢ` of the jobs (job `i` is the `i`-th entry), the
common due date `d`, and the threshold `y`. -/
abbrev EarlinessTardinessRestrictiveCommonDueDateInstance := List ℕ × ℕ × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed processing times. -/
abbrev Job (i : EarlinessTardinessRestrictiveCommonDueDateInstance) : Type := Fin i.1.length

/-- The processing time `pᵢ` of job `j`. -/
def processingTime (i : EarlinessTardinessRestrictiveCommonDueDateInstance) (j : Job i) : ℕ :=
  i.1.get j

/-- Completion times `C` form a single-machine schedule from time `0` for processing times
`p`: every job starts at or after time `0`, and of any two distinct jobs one completes before
the other starts. -/
def IsSchedule {n : ℕ} (p : Fin n → ℕ) (C : Fin n → ℝ) : Prop :=
  (∀ j, (p j : ℝ) ≤ C j) ∧ ∀ a b, a ≠ b → C a ≤ C b - p b ∨ C b ≤ C a - p a

/-- Well-formedness of an instance: every processing time is positive, and the common due
date is restrictive, `d < ∑ pᵢ`. -/
def WellFormed (i : EarlinessTardinessRestrictiveCommonDueDateInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p) ∧ i.2.1 < i.1.sum

/-- Some schedule has `∑ᵢ |Cᵢ - d| ≤ y`. -/
def EarlinessTardinessRestrictiveCommonDueDateFeasible
    (i : EarlinessTardinessRestrictiveCommonDueDateInstance) : Prop :=
  ∃ C : Job i → ℝ, IsSchedule (processingTime i) C ∧ ∑ j, |C j - i.2.1| ≤ i.2.2

open Classical in
/-- EARLINESS-TARDINESS WITH A RESTRICTIVE COMMON DUE DATE as a decision problem over
bitstrings. -/
noncomputable def earlinessTardinessRestrictiveCommonDueDateDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EarlinessTardinessRestrictiveCommonDueDateInstance) x with
  | some i => decide (WellFormed i ∧ EarlinessTardinessRestrictiveCommonDueDateFeasible i)
  | none => false

/-- **EARLINESS-TARDINESS WITH A RESTRICTIVE COMMON DUE DATE is NP-complete.** Source: Hall,
Kubiak, and Sethi (1991); Hoogeveen and van de Velde (1991), Theorem 3. -/
public theorem_wanted earlinessTardinessRestrictiveCommonDueDate_npComplete :
    earlinessTardinessRestrictiveCommonDueDateDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L earlinessTardinessRestrictiveCommonDueDateDec

end MetaMathlibExt.Complexity.NPComplete.EarlinessTardinessRestrictiveCommonDueDate
