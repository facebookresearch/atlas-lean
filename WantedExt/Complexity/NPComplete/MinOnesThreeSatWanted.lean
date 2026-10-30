/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM ONES 3-SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), MINIMUM ONES 3-SAT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinOnesThreeSat

/-!
# MINIMUM ONES 3-SAT is NP-complete

A 3-CNF formula and a bound `K`. The question is whether some satisfying assignment sets at
most `K` variables to true.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A MIN-ONES 3-SAT instance: number of variables, 3-CNF formula, bound. -/
abbrev MinOnesThreeSatInstance := ℕ × Cslib.Logic.PL.CNF × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : MinOnesThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2.1, clause.length = 3 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- A satisfying assignment with at most `K` true variables. -/
def MinOnesThreeSatFeasible
    (i : MinOnesThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    (Cslib.Logic.PL.CNF.Satisfies (fun x => assign.getD x false) i.2.1) ∧
    (assign.filter (fun b => b)).length ≤ i.2.2

open Classical in
/-- MINIMUM ONES 3-SAT as a decision problem over bitstrings. -/
noncomputable def minOnesThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinOnesThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ MinOnesThreeSatFeasible i)
  | none => false

/-- **MINIMUM ONES 3-SAT is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability: A Guide to the Theory of NP-Completeness* (1979), MINIMUM ONES 3-SAT. -/
public theorem_wanted minOnesThreeSat_npComplete :
    minOnesThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minOnesThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.MinOnesThreeSat
