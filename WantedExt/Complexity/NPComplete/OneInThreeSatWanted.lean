/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 1-IN-3-SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), ONE-IN-THREE 3-SAT; T. J. Schaefer, "The complexity of satisfiability
problems" (1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OneInThreeSat

/-!
# 1-IN-3-SAT is NP-complete

A 3-CNF formula: every clause has exactly three literals. The question is whether some
assignment makes exactly one literal true in every clause.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A 1-in-3-SAT instance: number of variables, 3-CNF formula. -/
abbrev OneInThreeSatInstance := ℕ × Cslib.Logic.PL.CNF

/-- Well-formedness of an instance. -/
def WellFormed (i : OneInThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length = 3 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- An assignment making exactly one literal true per clause. -/
def OneInThreeSatFeasible
    (i : OneInThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    ∀ clause ∈ i.2, ∃ k < clause.length,
      Cslib.Logic.PL.CNFLiteral.Satisfies (fun x => assign.getD x false)
        (clause.getD k (0, false)) ∧
        ∀ j < clause.length,
          Cslib.Logic.PL.CNFLiteral.Satisfies (fun x => assign.getD x false)
            (clause.getD j (0, false)) → j = k

open Classical in
/-- 1-IN-3-SAT as a decision problem over bitstrings. -/
noncomputable def oneInThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OneInThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ OneInThreeSatFeasible i)
  | none => false

/-- **1-IN-3-SAT is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability: A Guide to the Theory of NP-Completeness* (1979), ONE-IN-THREE 3-SAT; T.
J. Schaefer, "The complexity of satisfiability problems" (1978). -/
public theorem_wanted oneInThreeSat_npComplete :
    oneInThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L oneInThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.OneInThreeSat
