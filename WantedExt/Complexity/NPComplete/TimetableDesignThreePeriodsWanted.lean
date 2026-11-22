/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TIMETABLE DESIGN with three work periods is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 243, problem [SS19] TIMETABLE
DESIGN, comment: "Remains NP-complete even if `|H| = 3`, `A(t) = H` for all `t ∈ T`, and each
`R(c, t) ∈ {0, 1}`";
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048 (the reference Garey and Johnson give for [SS19]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TimetableDesignWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TimetableDesignThreePeriods

open MetaMathlibExt.Complexity.NPComplete.TimetableDesign

/-!
# TIMETABLE DESIGN with three work periods is NP-complete

INSTANCE: a set `H` of three "work periods", a set `C` of "craftsmen", a set `T` of "tasks",
a subset `A(c) ⊆ H` of "available hours" for each craftsman `c ∈ C`, `A(t) = H` for each task
`t ∈ T`, and, for each pair `(c, t) ∈ C × T`, a number `R(c, t) ∈ {0, 1}` of "required work
periods". QUESTION: is there a timetable `f : C × T × H → {0, 1}` satisfying conditions
(1)-(4) of TIMETABLE DESIGN?

This is the restriction of TIMETABLE DESIGN
(`WantedExt.Complexity.NPComplete.TimetableDesignWanted`) to instances with `|H| = 3`, every
task available in every period, and every requirement in `{0, 1}`. The instance type, its
`WellFormed` and `TimetableDesignFeasible` are reused unchanged; the restriction is added to
well-formedness. `A(t) = H` says that every period `h < |H|` occurs in the list `A(t)`
(`WellFormed` already puts every listed hour in `H`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance of the restriction: the instance is a well-formed TIMETABLE
DESIGN instance, `|H| = 3`, every task's list of available hours contains every period, and
every requirement `R(c, t)` is `0` or `1`. -/
def RestrictedWellFormed (i : TimetableDesignInstance) : Prop :=
  WellFormed i ∧ i.1 = 3 ∧ (∀ a ∈ i.2.2.2.2.1, ∀ h < i.1, h ∈ a) ∧
    ∀ row ∈ i.2.2.2.2.2, ∀ r ∈ row, r ≤ 1

open Classical in
/-- TIMETABLE DESIGN with three work periods, as a decision
problem over bitstrings. -/
noncomputable def timetableDesignThreePeriodsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TimetableDesignInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ TimetableDesignFeasible i)
  | none => false

/-- **TIMETABLE DESIGN remains NP-complete with `|H| = 3`, `A(t) = H` for every task, and
`R(c, t) ∈ {0, 1}`.** Source: Garey and Johnson (1979), [SS19], comment; Even, Itai, and Shamir
(1976). -/
public theorem_wanted timetableDesignThreePeriods_npComplete :
    timetableDesignThreePeriodsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L timetableDesignThreePeriodsDec

end MetaMathlibExt.Complexity.NPComplete.TimetableDesignThreePeriods
