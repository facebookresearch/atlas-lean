/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM NUMBER OF SATISFIABLE FORMULAS: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM NUMBER OF SATISFIABLE FORMULAS (decision version);
V. Kann, "Polynomially bounded minimization problems which are hard to approximate", Proc.
20th ICALP, LNCS 700 (1993), 52-63, doi:10.1007/3-540-56939-1_61;
R. Kohli, R. Krishnamurti, and P. Mirchandani, "The minimum satisfiability problem", SIAM
Journal on Discrete Mathematics 7 (1994), 275-283, doi:10.1137/S0895480191220836.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumNumberOfSatisfiableFormulas

/-- An instance: the number `n` of variables, the formulas in order, and the bound `K`. -/
abbrev MinimumNumberOfSatisfiableFormulasInstance := ℕ × List Cslib.Logic.LegacyPL.CNF × ℕ

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
      Cslib.Logic.LegacyPL.CNF.Satisfies (fun x => assign.getD x false) (i.2.1.get j)).card ≤ i.2.2

open Classical in
/-- MINIMUM NUMBER OF SATISFIABLE FORMULAS as a decision problem over bitstrings. -/
noncomputable def minimumNumberOfSatisfiableFormulasDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumNumberOfSatisfiableFormulasInstance) x with
  | some i => decide (WellFormed i ∧ MinimumNumberOfSatisfiableFormulasFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumNumberOfSatisfiableFormulas
