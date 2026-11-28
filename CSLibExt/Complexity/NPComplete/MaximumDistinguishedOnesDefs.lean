/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM DISTINGUISHED ONES: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM DISTINGUISHED ONES;
V. Kann, *On the Approximability of NP-complete Optimization Problems*, PhD thesis, Royal
Institute of Technology, Stockholm (1992), problem [7.13] Max distinguished ones;
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

namespace MetaMathlibExt.Complexity.NPComplete.MaximumDistinguishedOnes

/-- An instance: `|X|`, `|Z|`, the clauses `C`, and the bound `K`. -/
abbrev MaximumDistinguishedOnesInstance := ℕ × ℕ × Cslib.Logic.LegacyPL.CNF × ℕ

/-- Well-formedness of an instance: every clause has at most three literals, all over the
variables `0, …, |X| + |Z| - 1`, and `K` is positive. -/
def WellFormed (i : MaximumDistinguishedOnesInstance) : Prop :=
  (∀ clause ∈ i.2.2.1, clause.length ≤ 3 ∧ ∀ l ∈ clause, l.1 < i.1 + i.2.1) ∧ 0 < i.2.2.2

/-- Some assignment satisfies every clause and sets at least `K` variables of `Z` to true. -/
def MaximumDistinguishedOnesFeasible (i : MaximumDistinguishedOnesInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 + i.2.1 ∧
    Cslib.Logic.LegacyPL.CNF.Satisfies (fun x => assign.getD x false) i.2.2.1 ∧
    i.2.2.2 ≤ ((List.range i.2.1).filter fun j => assign.getD (i.1 + j) false).length

open Classical in
/-- MAXIMUM DISTINGUISHED ONES as a decision problem over bitstrings. -/
noncomputable def maximumDistinguishedOnesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumDistinguishedOnesInstance) x with
  | some i => decide (WellFormed i ∧ MaximumDistinguishedOnesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumDistinguishedOnes
