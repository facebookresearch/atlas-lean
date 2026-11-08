/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM 2-SATISFIABILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), MINIMUM 2-SATISFIABILITY; R. Kohli, R. Krishnamurti, and P. Mirchandani,
"The minimum satisfiability problem" (1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinTwoSat

/-!
# MINIMUM 2-SATISFIABILITY is NP-complete

A 2-CNF formula (every clause has at most two literals) and a bound `K`. The question is
whether some assignment satisfies at most `K` clauses.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A MIN-2SAT instance: number of variables, 2-CNF formula, bound. -/
abbrev MinTwoSatInstance := ℕ × Cslib.Logic.PL.CNF × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : MinTwoSatInstance) : Prop :=
  (∀ clause ∈ i.2.1, clause.length ≤ 2 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- An assignment satisfying at most `K` clauses. -/
def MinTwoSatFeasible
    (i : MinTwoSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∃ S : Finset ℕ, S ⊆ Finset.range i.2.1.length ∧ S.card ≤ i.2.2 ∧
      ∀ j < i.2.1.length,
        Cslib.Logic.PL.CNFClause.Satisfies (fun x => assign.getD x false)
          (i.2.1.getD j []) ↔ j ∈ S

open Classical in
/-- MINIMUM 2-SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def minTwoSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinTwoSatInstance) x with
  | some i => decide (WellFormed i ∧ MinTwoSatFeasible i)
  | none => false

/-- **MINIMUM 2-SATISFIABILITY is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability: A Guide to the Theory of NP-Completeness* (1979), MINIMUM
2-SATISFIABILITY; R. Kohli, R. Krishnamurti, and P. Mirchandani, "The minimum
satisfiability problem" (1994). -/
public theorem_wanted minTwoSat_npComplete :
    minTwoSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minTwoSatDec

end MetaMathlibExt.Complexity.NPComplete.MinTwoSat
