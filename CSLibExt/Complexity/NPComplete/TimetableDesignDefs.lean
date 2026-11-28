/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TIMETABLE DESIGN: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS19] TIMETABLE
DESIGN;
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TimetableDesign

/-- An instance: the numbers `|H|`, `|C|`, `|T|` of work periods, craftsmen and tasks, the
lists `A(c)` of available hours of the craftsmen, the lists `A(t)` of available hours of the
tasks, and the requirement matrix `R`, one row `[R(c, 0), …, R(c, |T| - 1)]` per craftsman. -/
abbrev TimetableDesignInstance :=
  ℕ × ℕ × ℕ × List (List ℕ) × List (List ℕ) × List (List ℕ)

/-- Well-formedness of an instance: there is one list of available hours per craftsman and
per task, every available hour lies in `H`, and `R` is a `|C| × |T|` matrix. -/
def WellFormed (i : TimetableDesignInstance) : Prop :=
  i.2.2.2.1.length = i.2.1 ∧ (∀ a ∈ i.2.2.2.1, ∀ h ∈ a, h < i.1) ∧
    i.2.2.2.2.1.length = i.2.2.1 ∧ (∀ a ∈ i.2.2.2.2.1, ∀ h ∈ a, h < i.1) ∧
    i.2.2.2.2.2.length = i.2.1 ∧ ∀ row ∈ i.2.2.2.2.2, row.length = i.2.2.1

/-- There is a timetable `f : C × T × H → {0, 1}` satisfying conditions (1)-(4). -/
def TimetableDesignFeasible (i : TimetableDesignInstance) : Prop :=
  ∃ f : Fin i.2.1 → Fin i.2.2.1 → Fin i.1 → Bool,
    (∀ c t h, f c t h = true →
      (h : ℕ) ∈ i.2.2.2.1.getD c [] ∧ (h : ℕ) ∈ i.2.2.2.2.1.getD t []) ∧
    (∀ h c t t', f c t h = true → f c t' h = true → t = t') ∧
    (∀ h t c c', f c t h = true → f c' t h = true → c = c') ∧
    ∀ c t, (Finset.univ.filter fun h => f c t h = true).card =
      (i.2.2.2.2.2.getD c []).getD t 0

open Classical in
/-- TIMETABLE DESIGN as a decision problem over bitstrings. -/
noncomputable def timetableDesignDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TimetableDesignInstance) x with
  | some i => decide (WellFormed i ∧ TimetableDesignFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TimetableDesign
