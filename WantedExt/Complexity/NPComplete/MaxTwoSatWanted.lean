/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM 2-SATISFIABILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), MAXIMUM 2-SATISFIABILITY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxTwoSat

/-!
# MAXIMUM 2-SATISFIABILITY is NP-complete

A 2-CNF formula (every clause has at most two literals) and a bound `K`. The question is
whether some assignment satisfies at least `K` clauses.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A MAX-2SAT instance: number of variables, 2-CNF formula, bound. -/
abbrev MaxTwoSatInstance := ℕ × Cslib.Logic.PL.CNF × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : MaxTwoSatInstance) : Prop :=
  (∀ clause ∈ i.2.1, clause.length ≤ 2 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- An assignment satisfying at least `K` clauses. -/
def MaxTwoSatFeasible
    (i : MaxTwoSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∃ sub : Cslib.Logic.PL.CNF, sub.Sublist i.2.1 ∧ i.2.2 ≤ sub.length ∧
      ∀ clause ∈ sub, Cslib.Logic.PL.CNFClause.Satisfies
        (fun x => assign.getD x false) clause

open Classical in
/-- MAXIMUM 2-SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def maxTwoSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxTwoSatInstance) x with
  | some i => decide (WellFormed i ∧ MaxTwoSatFeasible i)
  | none => false

/-- **MAXIMUM 2-SATISFIABILITY is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability: A Guide to the Theory of NP-Completeness* (1979), MAXIMUM
2-SATISFIABILITY. -/
public theorem_wanted maxTwoSat_npComplete :
    maxTwoSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxTwoSatDec

end MetaMathlibExt.Complexity.NPComplete.MaxTwoSat
