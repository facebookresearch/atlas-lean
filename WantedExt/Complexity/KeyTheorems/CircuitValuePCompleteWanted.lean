/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Circuit Value Problem is P-complete

Source:
R. E. Ladner, "The circuit value problem is log space complete for P", SIGACT News 7 (1975),
18-20; S. A. Cook, "A hierarchy for nondeterministic time complexity", Journal of Computer and
System Sciences 7 (1973), 343-353.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.CircuitValuePComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# The Circuit Value Problem is P-complete

The Circuit Value Problem (CVP): given a Boolean circuit (a list of gates) and an assignment
to its inputs, does the circuit output `true`? It is in `P` (evaluate the gates in order)
and `P`-hard under log-space many-one reductions: every polynomial-time computation can be
unrolled into a polynomial-size circuit, and the unrolling is log-space computable.
Log-space reductions are essential here: under polynomial-time reductions every nontrivial
problem in `P` would be `P`-complete. A gate is encoded as `(kind, refs)`: kind `0` is an
input variable (refs `[i]`), kind `1` a constant (refs `[b]`, true iff `b = 1`), kind `2`
negation, kind `3` conjunction, kind `4` disjunction; other kinds evaluate to `false`.
-/

/-- **Encoded circuit gates.** An encoded gate of a flat Boolean circuit is a pair $(k, r)$ of a
natural number $k$, the kind of the gate, and a list $r$ of natural numbers, its references.

Such a pair is read as a gate by the shared (kind, references) decoding of flat circuit gates. -/
abbrev CVGate := ℕ × List ℕ

/-- **Evaluation of an encoded Boolean circuit.** Let $n$ be a number of inputs, let $C$ be a
list of gates, each encoded as a (kind, references) pair, and let $a = (a_0, a_1, \dots)$ be a
list of booleans. The evaluation of $C$ on $a$ is the list of values of all gates, in order, of
the flat Boolean circuit on $n$ inputs obtained by decoding each pair of $C$, under the
assignment that sends each input $i < n$ to $a_i$, or to false when $i$ is at least the length
of $a$. -/
def cvCircuitEval {n : ℕ} (C : List CVGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := n))) (fun i => assign.getD i.val false)

/-- **Well-formed encoded circuits.** A list $C$ of encoded gates, each a (kind, references)
pair, is well formed as a circuit on $n$ inputs when the flat Boolean circuit on $n$ inputs
obtained by decoding each pair of $C$ is well formed: every decoded gate references only strictly
earlier gates. -/
def CVWellFormed {n : ℕ} (C : List CVGate) : Prop :=
  WellFormedCircuit (C.map (acGateOfPair (n := n)))

open Classical in
/-- **The Circuit Value Problem.** The Circuit Value Problem is the decision problem that accepts
a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of such triples,
to a triple $(n, C, a)$ of a natural number $n$, a list $C$ of encoded gates and a list $a$ of
booleans such that the flat Boolean circuit on $n$ inputs obtained by decoding the gates of $C$
is well formed, $a$ has length $n$, and the evaluation of $C$ on $a$ is a nonempty list whose
last entry is true. It rejects every bitstring that does not decode. -/
noncomputable def cvpDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List CVGate × List Bool) x with
  | some i => decide (CVWellFormed (n := i.1) i.2.1 ∧ i.2.2.length = i.1 ∧
      (cvCircuitEval (n := i.1) i.2.1 i.2.2).getLast? = some true)
  | none => false

/-- **The Circuit Value Problem is P-complete.** The Circuit Value Problem is in P, and every
decision problem in P is log-space many-one reducible to the Circuit Value Problem.

Source: R. E. Ladner, "The circuit value
problem is log space complete for P", SIGACT News 7 (1975), 18-20; S. A. Cook, "A hierarchy
for nondeterministic time complexity", Journal of Computer and System Sciences 7 (1973),
343-353. -/
public theorem_wanted cvp_p_complete :
    cvpDec ∈ MetaMathlibExt.ComplexityTheory.P ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.P → LogSpaceRed L cvpDec

end MetaMathlibExt.Complexity.KeyTheorems.CircuitValuePComplete
