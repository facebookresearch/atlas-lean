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

/-- A gate of a flat Boolean circuit, encoded as `(kind, refs)`: the shared
serial encoding of `Cslib.Complexity.Classes.acGateOfPair`/`acGateToPair`
(see `CSLibExt/Computability/Complexity/Classes.lean`). -/
abbrev CVGate := ℕ × List ℕ

/-- Values of all gates of an encoded circuit, in order: the shared typed
evaluator `circuitEval` on the decoded gates. The typed assignment is the
`List Bool` assignment restricted to the declared input count. -/
def cvCircuitEval {n : ℕ} (C : List CVGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := n))) (fun i => assign.getD i.val false)

/-- Well-formedness: the decoded circuit is a `WellFormedCircuit`. -/
def CVWellFormed {n : ℕ} (C : List CVGate) : Prop :=
  WellFormedCircuit (C.map (acGateOfPair (n := n)))

open Classical in
/-- The Circuit Value Problem as a decision problem over bitstrings,
decoding to `(input count, gates, assignment)`. -/
noncomputable def cvpDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List CVGate × List Bool) x with
  | some i => decide (CVWellFormed (n := i.1) i.2.1 ∧ i.2.2.length = i.1 ∧
      (cvCircuitEval (n := i.1) i.2.1 i.2.2).getLast? = some true)
  | none => false

/-- **The Circuit Value Problem is P-complete.** Source: R. E. Ladner, "The circuit value
problem is log space complete for P", SIGACT News 7 (1975), 18-20; S. A. Cook, "A hierarchy
for nondeterministic time complexity", Journal of Computer and System Sciences 7 (1973),
343-353. -/
public theorem_wanted cvp_p_complete :
    cvpDec ∈ MetaMathlibExt.ComplexityTheory.P ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.P → LogSpaceRed L cvpDec

end MetaMathlibExt.Complexity.KeyTheorems.CircuitValuePComplete
