/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM NUMBER OF SATISFIABLE FORMULAS: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM NUMBER OF SATISFIABLE FORMULAS;
V. Kann, *On the Approximability of NP-complete Optimization Problems*, PhD thesis, Royal
Institute of Technology, Stockholm (1992), problem [7.12] and Theorem 4.32 (Max # Sat);
A. Panconesi and D. Ranjan, "Quantifiers and approximation", Theoretical Computer Science 107
(1993), 145-163, doi:10.1016/0304-3975(93)90259-V;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO2] 3-SATISFIABILITY (the special case described
below), from S. A. Cook, "The complexity of theorem-proving procedures", Proc. 3rd Annual ACM
Symposium on Theory of Computing (1971), 151-158, doi:10.1145/800157.805047.
-/
module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumNumberOfSatisfiableFormulas

/-- An instance: `|U|`, the formulas `C`, and the bound `K`. -/
abbrev MaximumNumberOfSatisfiableFormulasInstance := ℕ × List Cslib.Logic.LegacyPL.CNF × ℕ

/-- Well-formedness of an instance: every clause of every formula has at most three literals,
all over the variables `0, …, |U| - 1`, and `K` is positive. -/
def WellFormed (i : MaximumNumberOfSatisfiableFormulasInstance) : Prop :=
  (∀ F ∈ i.2.1, ∀ clause ∈ F, clause.length ≤ 3 ∧ ∀ l ∈ clause, l.1 < i.1) ∧ 0 < i.2.2

/-- Some assignment satisfies at least `K` of the formulas: a sublist (a choice of positions) of
at least `K` formulas, all satisfied. -/
def MaximumNumberOfSatisfiableFormulasFeasible
    (i : MaximumNumberOfSatisfiableFormulasInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∃ S : List Cslib.Logic.LegacyPL.CNF, S.Sublist i.2.1 ∧ i.2.2 ≤ S.length ∧
      ∀ F ∈ S, Cslib.Logic.LegacyPL.CNF.Satisfies (fun x => assign.getD x false) F

open Classical in
/-- MAXIMUM NUMBER OF SATISFIABLE FORMULAS as a decision problem over bitstrings. -/
noncomputable def maximumNumberOfSatisfiableFormulasDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumNumberOfSatisfiableFormulasInstance) x with
  | some i => decide (WellFormed i ∧ MaximumNumberOfSatisfiableFormulasFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumNumberOfSatisfiableFormulas
