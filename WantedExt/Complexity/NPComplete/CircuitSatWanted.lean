/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CIRCUIT SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), CIRCUIT SATISFIABILITY; S. A. Cook, "The complexity of theorem-proving
procedures" (1971).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircuitSat

/-!
# CIRCUIT SAT is NP-complete

A circuit is a list of gates. Gate `0` is AND, `1` is OR, `2` is NOT (second input ignored and
unconstrained), `3` is the variable with the given index, `4` is constant true, `5` is constant
false (both inputs ignored and unconstrained). A gate's used inputs refer either to a variable
index (below the number of variables) or to an earlier gate (variable count plus gate index).
The question is whether some assignment to the variables makes the output of the last gate
true. The empty circuit has no output and is a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A circuit-satisfiability instance: number of variables, list of gates (operation, first
input, second input). -/
abbrev CircuitSatInstance := ℕ × List (ℕ × ℕ × ℕ)


/-- Resolve a circuit reference: a variable index, or an earlier gate value. -/
def CircuitRef (assign : List Bool) (vals : List Bool) (idx : ℕ) : Bool :=
  if idx < assign.length then assign.getD idx false
  else vals.getD (idx - assign.length) false

/-- The value of one gate, given the assignment and earlier gate values. -/
def GateValue (assign : List Bool) (vals : List Bool) (gate : ℕ × ℕ × ℕ) : Bool :=
  match gate.1 with
  | 0 => CircuitRef assign vals gate.2.1 && CircuitRef assign vals gate.2.2
  | 1 => CircuitRef assign vals gate.2.1 || CircuitRef assign vals gate.2.2
  | 2 => !CircuitRef assign vals gate.2.1
  | 3 => assign.getD gate.2.1 false
  | 4 => true
  | _ => false

/-- Gate values in order. -/
def EvalCircuit (assign : List Bool) (gates : List (ℕ × ℕ × ℕ)) : List Bool :=
  gates.foldl (fun vals gate => vals ++ [GateValue assign vals gate]) []


/-- Well-formedness of an instance. -/
def WellFormed (i : CircuitSatInstance) : Prop :=
  (∀ p ∈ i.2.zipIdx, p.1.1 ≤ 5 ∧
    ((p.1.1 = 0 ∨ p.1.1 = 1) → p.1.2.1 < i.1 + p.2 ∧ p.1.2.2 < i.1 + p.2) ∧
    (p.1.1 = 2 → p.1.2.1 < i.1 + p.2) ∧
    (p.1.1 = 3 → p.1.2.1 < i.1))

/-- A satisfying assignment: the last gate evaluates to true. -/
def CircuitSatFeasible
    (i : CircuitSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    (EvalCircuit assign i.2).getLast? = some true

open Classical in
/-- CIRCUIT SAT as a decision problem over bitstrings. -/
noncomputable def circuitSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CircuitSatInstance) x with
  | some i => decide (WellFormed i ∧ CircuitSatFeasible i)
  | none => false

/-- **CIRCUIT SAT is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability: A Guide to the Theory of NP-Completeness* (1979), CIRCUIT SATISFIABILITY;
S. A. Cook, "The complexity of theorem-proving procedures" (1971). -/
public theorem_wanted circuitSat_npComplete :
    circuitSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circuitSatDec

end MetaMathlibExt.Complexity.NPComplete.CircuitSat
