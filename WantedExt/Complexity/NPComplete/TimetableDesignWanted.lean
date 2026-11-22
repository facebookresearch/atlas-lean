/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TIMETABLE DESIGN is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS19] TIMETABLE
DESIGN;
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TimetableDesign

/-!
# TIMETABLE DESIGN is NP-complete

INSTANCE: a set `H` of "work periods", a set `C` of "craftsmen", a set `T` of "tasks", a
subset `A(c) ⊆ H` of "available hours" for each craftsman `c ∈ C`, a subset `A(t) ⊆ H` of
"available hours" for each task `t ∈ T`, and, for each pair `(c, t) ∈ C × T`, a number
`R(c, t) ∈ ℤ₀⁺` of "required work periods".
QUESTION: is there a timetable for completing all the tasks, i.e., a function
`f : C × T × H → {0, 1}` (where `f(c, t, h) = 1` means that craftsman `c` works on task `t`
during period `h`) such that (1) `f(c, t, h) = 1` only if `h ∈ A(c) ∩ A(t)`, (2) for each
`h ∈ H` and `c ∈ C` there is at most one `t ∈ T` for which `f(c, t, h) = 1`, (3) for each
`h ∈ H` and `t ∈ T` there is at most one `c ∈ C` for which `f(c, t, h) = 1`, and (4) for each
pair `(c, t) ∈ C × T` there are exactly `R(c, t)` values of `h` for which `f(c, t, h) = 1`?

The sets are `H = Fin |H|`, `C = Fin |C|` and `T = Fin |T|`, and `{0, 1}` is `Bool`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TIMETABLE DESIGN is NP-complete.** Source: Garey and Johnson (1979), [SS19]; Even, Itai,
and Shamir (1976). -/
public theorem_wanted timetableDesign_npComplete :
    timetableDesignDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L timetableDesignDec

end MetaMathlibExt.Complexity.NPComplete.TimetableDesign
