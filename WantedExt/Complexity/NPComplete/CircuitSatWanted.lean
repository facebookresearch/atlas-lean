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

/-- **Circuit-satisfiability instances.** An instance of circuit satisfiability is a pair $(n, G)$
of a natural number $n$, the number of variables, and a finite list $G$ of gates, each gate a
triple $(o, a, b)$ of natural numbers: an operation code $o$, a first input $a$ and a second
input $b$. -/
abbrev CircuitSatInstance := ℕ × List (ℕ × ℕ × ℕ)


/-- **Resolving a circuit input.** Given an assignment $x = (x_0, \dots, x_{n-1})$ of booleans to
the variables and the list $v = (v_0, \dots, v_{k-1})$ of the values of the gates evaluated so
far, an input index $r$ resolves to $x_r$ if $r < n$, to $v_{r-n}$ if $n \le r < n + k$, and to
false if $r \ge n + k$. -/
def CircuitRef (assign : List Bool) (vals : List Bool) (idx : ℕ) : Bool :=
  if idx < assign.length then assign.getD idx false
  else vals.getD (idx - assign.length) false

/-- **Value of a gate.** Let $x = (x_0, \dots, x_{n-1})$ be an assignment of booleans to the
variables and $v$ the list of values of the earlier gates. An input index $r$ resolves to $x_r$ if
$r < n$, and otherwise to $v_{r-n}$, or to false if that entry does not exist. The value of a gate
$(o, a, b)$ is the conjunction of the resolved inputs $a$ and $b$ if $o = 0$, their disjunction
if $o = 1$, the negation of the resolved input $a$ if $o = 2$, $x_a$ (false if $a \ge n$) if
$o = 3$, true if $o = 4$, and false if $o \ge 5$. -/
def GateValue (assign : List Bool) (vals : List Bool) (gate : ℕ × ℕ × ℕ) : Bool :=
  match gate.1 with
  | 0 => CircuitRef assign vals gate.2.1 && CircuitRef assign vals gate.2.2
  | 1 => CircuitRef assign vals gate.2.1 || CircuitRef assign vals gate.2.2
  | 2 => !CircuitRef assign vals gate.2.1
  | 3 => assign.getD gate.2.1 false
  | 4 => true
  | _ => false

/-- **Evaluating a circuit.** Given an assignment of booleans to the variables and a list of gates
$g_1, \dots, g_m$, circuit evaluation returns the list $(v_1, \dots, v_m)$ of gate values, where
$v_k$ is the value of the gate $g_k$ under the assignment and the earlier values
$(v_1, \dots, v_{k-1})$. -/
def EvalCircuit (assign : List Bool) (gates : List (ℕ × ℕ × ℕ)) : List Bool :=
  gates.foldl (fun vals gate => vals ++ [GateValue assign vals gate]) []


/-- **Well-formed circuit-satisfiability instances.** An instance $(n, G)$ with gates
$G = (g_0, \dots, g_{m-1})$ is well formed when every gate $g_j = (o, a, b)$ satisfies
$o \le 5$, and moreover: if $o = 0$ or $o = 1$ then $a < n + j$ and $b < n + j$; if $o = 2$ then
$a < n + j$; and if $o = 3$ then $a < n$. -/
def WellFormed (i : CircuitSatInstance) : Prop :=
  (∀ p ∈ i.2.zipIdx, p.1.1 ≤ 5 ∧
    ((p.1.1 = 0 ∨ p.1.1 = 1) → p.1.2.1 < i.1 + p.2 ∧ p.1.2.2 < i.1 + p.2) ∧
    (p.1.1 = 2 → p.1.2.1 < i.1 + p.2) ∧
    (p.1.1 = 3 → p.1.2.1 < i.1))

/-- **Satisfiable circuit instances.** An instance $(n, G)$ is satisfiable when there is an
assignment $x \in \{\mathrm{true}, \mathrm{false}\}^n$ of booleans to the $n$ variables such that
the evaluation of the circuit $G$ under $x$ has a last gate value and that value is true. In
particular an instance with no gates is not satisfiable. -/
def CircuitSatFeasible
    (i : CircuitSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    (EvalCircuit assign i.2).getLast? = some true

open Classical in
/-- **The CIRCUIT SAT decision problem.** CIRCUIT SAT is the decision problem that accepts a
bitstring $s$ exactly when $s$ decodes, under the canonical bitstring encoding of
circuit-satisfiability instances, to an instance that is well formed and satisfiable. Bitstrings
that fail to decode are rejected. -/
noncomputable def circuitSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CircuitSatInstance) x with
  | some i => decide (WellFormed i ∧ CircuitSatFeasible i)
  | none => false

/-- **CIRCUIT SAT is NP-complete.** The CIRCUIT SAT decision problem on bitstrings belongs to the
class NP, and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability: A Guide to the Theory of NP-Completeness* (1979), CIRCUIT SATISFIABILITY;
S. A. Cook, "The complexity of theorem-proving procedures" (1971). -/
public theorem_wanted circuitSat_npComplete :
    circuitSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circuitSatDec

end MetaMathlibExt.Complexity.NPComplete.CircuitSat
