/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM NUMBER OF SATISFIABLE FORMULAS is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM NUMBER OF SATISFIABLE FORMULAS (decision version);
V. Kann, "Polynomially bounded minimization problems which are hard to approximate", Proc.
20th ICALP, LNCS 700 (1993), 52-63, doi:10.1007/3-540-56939-1_61;
R. Kohli, R. Krishnamurti, and P. Mirchandani, "The minimum satisfiability problem", SIAM
Journal on Discrete Mathematics 7 (1994), 275-283, doi:10.1137/S0895480191220836.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumNumberOfSatisfiableFormulas

/-!
# MINIMUM NUMBER OF SATISFIABLE FORMULAS is NP-complete

INSTANCE: a set `U` of variables, a collection `C` of 3CNF formulas over `U`, and a bound
`K`. QUESTION: is there a truth assignment for `U` that satisfies at most `K` formulas of `C`?

This is the decision version of the compendium's MINIMUM NUMBER OF SATISFIABLE FORMULAS
(measure: the number of formulas satisfied), shown NPO PB-complete by Kann through a
transformation from MINIMUM DISTINGUISHED ONES. NP-hardness of the decision version also follows
from the case in which every formula is a single clause: that is MINIMUM SATISFIABILITY, which
Kohli, Krishnamurti, and Mirchandani (1994) prove strongly NP-hard already for clauses of at
most two literals.

A 3CNF formula is a conjunction of clauses of at most three literals each. The variables are
`0, …, n - 1`; formulas use the repository's `Cslib.Logic.PL.CNF` (a clause is a list of
literals `(variable, polarity)`) with its semantics `Cslib.Logic.PL.CNF.Satisfies`. The
formulas form a list, so a formula listed twice counts twice.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables, the formulas in order, and the bound `K`. -/
abbrev MinimumNumberOfSatisfiableFormulasInstance := ℕ × List Cslib.Logic.PL.CNF × ℕ

/-- Well-formedness of an instance: every clause of every formula has at most 3 literals, all
over variables below `n`. -/
def WellFormed (i : MinimumNumberOfSatisfiableFormulasInstance) : Prop :=
  ∀ φ ∈ i.2.1, ∀ clause ∈ φ, clause.length ≤ 3 ∧ ∀ l ∈ clause, l.1 < i.1

open Classical in
/-- Some assignment of the `n` variables satisfies at most `K` of the formulas. -/
def MinimumNumberOfSatisfiableFormulasFeasible
    (i : MinimumNumberOfSatisfiableFormulasInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    (Finset.univ.filter fun j : Fin i.2.1.length =>
      Cslib.Logic.PL.CNF.Satisfies (fun x => assign.getD x false) (i.2.1.get j)).card ≤ i.2.2

open Classical in
/-- MINIMUM NUMBER OF SATISFIABLE FORMULAS as a decision problem over bitstrings. -/
noncomputable def minimumNumberOfSatisfiableFormulasDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumNumberOfSatisfiableFormulasInstance) x with
  | some i => decide (WellFormed i ∧ MinimumNumberOfSatisfiableFormulasFeasible i)
  | none => false

/-- **MINIMUM NUMBER OF SATISFIABLE FORMULAS is NP-complete.** Source: Crescenzi and Kann,
MINIMUM NUMBER OF SATISFIABLE FORMULAS; Kann (1993); Kohli, Krishnamurti, and Mirchandani (1994). -/
public theorem_wanted minimumNumberOfSatisfiableFormulas_npComplete :
    minimumNumberOfSatisfiableFormulasDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumNumberOfSatisfiableFormulasDec

end MetaMathlibExt.Complexity.NPComplete.MinimumNumberOfSatisfiableFormulas
