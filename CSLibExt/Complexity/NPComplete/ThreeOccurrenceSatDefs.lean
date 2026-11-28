/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SATISFIABILITY with at most three literals per clause and three clauses per variable is: definitions
NP-complete

Source:
C. A. Tovey, "A simplified NP-complete satisfiability problem", Discrete Applied Mathematics
8(1) (1984), 85-89, doi:10.1016/0166-218X(84)90081-7, Theorem 2.1;
M. Breen-McKay, B. Lavallee and B. D. Sullivan, "Hardness of the generalized coloring numbers",
arXiv:2112.10562 (2021), Section 3 (records Tovey's Theorem 2.1: "SAT remains NP-complete when
restricted to instances with 2 or 3 variables per clause and at most 3 occurrences per
variable");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO1] SATISFIABILITY.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeOccurrenceSat

/-- An instance: the number `n` of variables and the CNF formula (its clauses). -/
abbrev ThreeOccurrenceSatInstance := ℕ × Cslib.Logic.LegacyPL.CNF

/-- Well-formedness of an instance: every clause has at most three literals, all on variables
`< n`, and every variable occurs in at most three clauses. The bound counts the clauses that
contain a variable, not its occurrences: a variable repeated within one clause counts once. -/
def WellFormed (i : ThreeOccurrenceSatInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length ≤ 3 ∧ ∀ l ∈ clause, l.1 < i.1) ∧
    ∀ v < i.1, (i.2.filter (fun clause => clause.any (fun l => l.1 == v))).length ≤ 3

/-- A satisfying truth assignment. -/
def ThreeOccurrenceSatFeasible (i : ThreeOccurrenceSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.LegacyPL.CNF.Satisfies (fun x => assign.getD x false) i.2

open Classical in
/-- SATISFIABILITY with at most three literals per clause and three clauses per variable as a
decision problem over bitstrings. -/
noncomputable def threeOccurrenceSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeOccurrenceSatInstance) x with
  | some i => decide (WellFormed i ∧ ThreeOccurrenceSatFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeOccurrenceSat
