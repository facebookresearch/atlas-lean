/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BINARY CONSTRAINT SATISFACTION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), CONSTRAINT SATISFACTION; R. Dechter, *Constraint Processing* (2003).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BinaryCsp

/-!
# BINARY CONSTRAINT SATISFACTION is NP-complete

Variables with finite explicit domains, and binary constraints given by lists of allowed value
pairs. The question is whether there is an assignment giving every variable a value in its
domain and satisfying every constraint.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A binary CSP instance: variable domains, binary constraints (first variable, second
variable, allowed pairs). -/
abbrev BinaryCspInstance := List (List ℕ) × List (ℕ × ℕ × List (ℕ × ℕ))

/-- Well-formedness of an instance. -/
def WellFormed (i : BinaryCspInstance) : Prop :=
  (∀ c ∈ i.2, c.1 < i.1.length ∧ c.2.1 < i.1.length)

/-- An assignment satisfying all domains and constraints. -/
def BinaryCspFeasible
    (i : BinaryCspInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1.length ∧
    (∀ d < i.1.length, assign.getD d 0 ∈ i.1.getD d []) ∧
    ∀ c ∈ i.2, (assign.getD c.1 0, assign.getD c.2.1 0) ∈ c.2.2

open Classical in
/-- BINARY CONSTRAINT SATISFACTION as a decision problem over bitstrings. -/
noncomputable def binaryCspDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BinaryCspInstance) x with
  | some i => decide (WellFormed i ∧ BinaryCspFeasible i)
  | none => false

/-- **BINARY CONSTRAINT SATISFACTION is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability: A Guide to the Theory of NP-Completeness* (1979),
CONSTRAINT SATISFACTION; R. Dechter, *Constraint Processing* (2003). -/
public theorem_wanted binaryCsp_npComplete :
    binaryCspDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L binaryCspDec

end MetaMathlibExt.Complexity.NPComplete.BinaryCsp
