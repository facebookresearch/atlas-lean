/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM SATISFIABILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), MAXIMUM SATISFIABILITY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxSat

/-!
# MAXIMUM SATISFIABILITY is NP-complete

A CNF formula (clauses of any length) and a bound `K`. The question is whether some assignment
satisfies at least `K` clauses.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A MAX-SAT instance: number of variables, CNF formula, bound. -/
abbrev MaxSatInstance := ℕ × Cslib.Logic.PL.CNF × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : MaxSatInstance) : Prop :=
  (∀ clause ∈ i.2.1, ∀ l ∈ clause, l.1 < i.1)

/-- An assignment satisfying at least `K` clauses. -/
def MaxSatFeasible
    (i : MaxSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∃ sub : Cslib.Logic.PL.CNF, sub.Sublist i.2.1 ∧ i.2.2 ≤ sub.length ∧
      ∀ clause ∈ sub, Cslib.Logic.PL.CNFClause.Satisfies
        (fun x => assign.getD x false) clause

open Classical in
/-- MAXIMUM SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def maxSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxSatInstance) x with
  | some i => decide (WellFormed i ∧ MaxSatFeasible i)
  | none => false

/-- **MAXIMUM SATISFIABILITY is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability: A Guide to the Theory of NP-Completeness* (1979), MAXIMUM
SATISFIABILITY. -/
public theorem_wanted maxSat_npComplete :
    maxSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxSatDec

end MetaMathlibExt.Complexity.NPComplete.MaxSat
