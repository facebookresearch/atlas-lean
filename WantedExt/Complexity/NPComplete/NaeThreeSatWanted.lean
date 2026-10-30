/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NOT-ALL-EQUAL 3-SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), NOT-ALL-EQUAL 3-SAT; T. J. Schaefer, "The complexity of satisfiability
problems" (1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NaeThreeSat

/-!
# NOT-ALL-EQUAL 3-SAT is NP-complete

A 3-CNF formula: every clause has exactly three literals. The question is whether some
assignment makes every clause not-all-equal, that is, each clause has both a true and a false
literal.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A not-all-equal 3-SAT instance: number of variables, 3-CNF formula. -/
abbrev NaeThreeSatInstance := ℕ × Cslib.Logic.PL.CNF

/-- Well-formedness of an instance. -/
def WellFormed (i : NaeThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length = 3 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- An assignment making every clause not-all-equal. -/
def NaeThreeSatFeasible
    (i : NaeThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∀ clause ∈ i.2, Cslib.Logic.PL.CNFClause.Satisfies (fun x => assign.getD x false) clause ∧
      ∃ l ∈ clause, ¬ Cslib.Logic.PL.CNFLiteral.Satisfies (fun x => assign.getD x false) l

open Classical in
/-- NOT-ALL-EQUAL 3-SAT as a decision problem over bitstrings. -/
noncomputable def naeThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NaeThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ NaeThreeSatFeasible i)
  | none => false

/-- **NOT-ALL-EQUAL 3-SAT is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability: A Guide to the Theory of NP-Completeness* (1979), NOT-ALL-EQUAL 3-SAT;
T. J. Schaefer, "The complexity of satisfiability problems" (1978). -/
public theorem_wanted naeThreeSat_npComplete :
    naeThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L naeThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.NaeThreeSat
