/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SATISFIABILITY with at most three literals per clause and three clauses per variable is
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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeOccurrenceSat

/-!
# SATISFIABILITY with at most three literals per clause and three clauses per variable is
NP-complete

INSTANCE: a set `U` of variables and a collection `C` of clauses over `U` (as in [LO1]
SATISFIABILITY) such that every clause has at most `3` literals and every variable occurs in at
most `3` clauses.
QUESTION: is there a satisfying truth assignment for `C`?

Formulas are `Cslib.Logic.PL.CNF` (lists of clauses, a clause a list of literals
`(variable, sign)`), with satisfaction `Cslib.Logic.PL.CNF.Satisfies`, in the encoding of the
existing `WantedExt.Complexity.NPComplete.BoundedOccurrenceThreeSatWanted` (variables
`0, …, n - 1`; an assignment is a list of `n` truth values). A variable occurs in a clause when
one of the clause's literals is on it. Tovey's Theorem 2.1 is stated with clauses of two or three
literals and at most three occurrences per variable; those instances belong to this class, and
the bound three cannot be lowered (with every variable in at most two clauses the problem is
solvable in polynomial time). This differs from `BoundedOccurrenceThreeSatWanted`, whose clauses
have exactly three literals and whose variables occur at most four times (with exactly three
literals per clause and at most three occurrences, every formula is satisfiable).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables and the CNF formula (its clauses). -/
abbrev ThreeOccurrenceSatInstance := ℕ × Cslib.Logic.PL.CNF

/-- Well-formedness of an instance: every clause has at most three literals, all on variables
`< n`, and every variable occurs in at most three clauses. -/
def WellFormed (i : ThreeOccurrenceSatInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length ≤ 3 ∧ ∀ l ∈ clause, l.1 < i.1) ∧
    ∀ v < i.1, (i.2.filter (fun clause => clause.any (fun l => l.1 == v))).length ≤ 3

/-- A satisfying truth assignment. -/
def ThreeOccurrenceSatFeasible (i : ThreeOccurrenceSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.PL.CNF.Satisfies (fun x => assign.getD x false) i.2

open Classical in
/-- SATISFIABILITY with at most three literals per clause and three clauses per variable as a
decision problem over bitstrings. -/
noncomputable def threeOccurrenceSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeOccurrenceSatInstance) x with
  | some i => decide (WellFormed i ∧ ThreeOccurrenceSatFeasible i)
  | none => false

/-- **SATISFIABILITY with at most three literals per clause and three clauses per variable is
NP-complete.** Source: Tovey (1984), Theorem 2.1. -/
public theorem_wanted threeOccurrenceSat_npComplete :
    threeOccurrenceSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeOccurrenceSatDec

end MetaMathlibExt.Complexity.NPComplete.ThreeOccurrenceSat
