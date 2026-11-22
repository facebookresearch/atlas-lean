/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Succinct Circuit Value is EXP-complete

Source:
C. H. Papadimitriou, Computational Complexity, Addison-Wesley, 1994, Theorem 20.2 (succinct
versions of P-complete problems are EXP-complete); S. A. Cook, "A hierarchy for
nondeterministic time complexity", Journal of Computer and System Sciences 7 (1973),
343-353; R. E. Ladner, "The circuit value problem is log space complete for P", SIGACT
News 7 (1975), 18-20.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.SuccinctCircuitValueEXPComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Succinct Circuit Value is EXP-complete

A *succinctly described* circuit `D` with `2 ^ n` gates is given by an ordinary circuit `C`
with `n` inputs: on input `i` (as `n` bits), `C` outputs the description of gate `i` of `D`:
3 bits of gate type (`0` input, `1` AND, `2` OR, `3` NOT, `4` constant true, `5` constant
false), then `n` bits for the first predecessor index, then `n` bits for the second. The
first `n` gates of `D` are its input gates, fed by the `n`-bit string `x` given as part of
the instance; the problem asks whether the last gate of `D` outputs `true` on `x`. It is
`EXP`-complete: evaluating all `2 ^ n` gates takes exponential time, and every `EXP`
computation can be encoded. This is the EXP-complete analogue of the Circuit Value Problem;
unlike succinct SAT, there is no existential quantification over an exponentially long
assignment, which would make the problem NEXP-complete.
-/

/-- A gate of a flat Boolean circuit, encoded as `(kind, refs)`: the shared
serial encoding of `Cslib.Complexity.Classes.acGateOfPair`/`acGateToPair`. -/
abbrev SCVGate := ℕ × List ℕ

/-- Values of all gates of an encoded circuit, in order: the shared typed
evaluator `circuitEval` on the decoded gates, with the input count `n`. -/
def scvCircuitEval (C : List SCVGate) (assign : List Bool) (n : ℕ) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := n))) (fun i => assign.getD i.val false)

/-- The last `k` gate values of an encoded circuit on an assignment (its outputs). -/
def scvCircuitOutputs (C : List SCVGate) (assign : List Bool) (k n : ℕ) : List Bool :=
  let vals := scvCircuitEval C assign n
  vals.drop (vals.length - k)

/-- The `n`-bit binary expansion of `i`, least significant bit first. -/
def scvBitsOf (i n : ℕ) : List Bool :=
  (List.range n).map (fun k => decide ((i / 2 ^ k) % 2 = 1))

/-- The number with binary expansion `bs`, least significant bit first. -/
def scvBitsToNum : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * scvBitsToNum rest

/-- Description of gate `i` of the succinctly described circuit `D`: the `2 * n + 3` output
bits of `C` on the `n`-bit input `i`. -/
def succDesc (C : List SCVGate) (n i : ℕ) : List Bool :=
  scvCircuitOutputs C (scvBitsOf i n) (2 * n + 3) n

/-- Gate type (first 3 output bits), first predecessor, second predecessor of gate `i`. -/
def succGateInfo (C : List SCVGate) (n i : ℕ) : ℕ × ℕ × ℕ :=
  let outs := succDesc C n i
  (scvBitsToNum (outs.take 3), scvBitsToNum ((outs.drop 3).take n),
    scvBitsToNum (outs.drop (3 + n)))

/-- Value of gate `i` of `D`, given the values of earlier gates and the input assignment
`x` of length `n`: the first `n` gates are input gates fed by `x`. -/
def succGateVal (C : List SCVGate) (n : ℕ) (x : List Bool) (vs : List Bool)
    (i : ℕ) : Bool :=
  if i < n then x.getD i false
  else match succGateInfo C n i with
    | (1, p₁, p₂) => (vs.getD p₁ false) && (vs.getD p₂ false)
    | (2, p₁, p₂) => (vs.getD p₁ false) || (vs.getD p₂ false)
    | (3, p₁, _) => !(vs.getD p₁ false)
    | (4, _, _) => true
    | (5, _, _) => false
    | _ => false

/-- Values of all gates of the succinctly described circuit `D`, in order. -/
def succEval (C : List SCVGate) (n : ℕ) (x : List Bool) : List Bool :=
  (List.range (2 ^ n)).foldl (fun vs i => vs ++ [succGateVal C n x vs i]) []

/-- Well-formedness of the description circuit `C` on `n` inputs: at least
`2 * n + 3` gates (so the `2 * n + 3` outputs of `succDesc` exist; without
this, missing outputs would silently read as `false`), and the decoded
circuit is a `WellFormedCircuit`. -/
def succDescWellFormed (C : List SCVGate) (n : ℕ) : Prop :=
  2 * n + 3 ≤ C.length ∧ WellFormedCircuit (C.map (acGateOfPair (n := n)))

/-- Well-formedness: the first `n` gates of `D` are input gates (type `0`), and every
other non-constant gate references earlier gates. -/
def succWellFormed (C : List SCVGate) (n : ℕ) : Prop :=
  ∀ i, i < 2 ^ n →
    if i < n then (succGateInfo C n i).1 = 0
    else match succGateInfo C n i with
      | (4, _, _) => True
      | (5, _, _) => True
      | (_, p₁, p₂) => p₁ < i ∧ p₂ < i

open Classical in
/-- Succinct Circuit Value as a decision problem over bitstrings, decoding to
`(n, C, x)` with `x` of length `n`: does the last gate of `D` output `true` on `x`? -/
noncomputable def succinctCircuitValueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List SCVGate × List Bool) x with
  | some i => decide (i.2.2.length = i.1 ∧ succDescWellFormed i.2.1 i.1 ∧
      succWellFormed i.2.1 i.1 ∧
      (succEval i.2.1 i.1 i.2.2).getLast? = some true)
  | none => false

/-- **Succinct Circuit Value is EXP-complete.** Source: C. H. Papadimitriou, Computational
Complexity, Addison-Wesley, 1994, Theorem 20.2 (succinct versions of P-complete problems
are EXP-complete); S. A. Cook, "A hierarchy for nondeterministic time complexity",
Journal of Computer and System Sciences 7 (1973), 343-353; R. E. Ladner, "The circuit
value problem is log space complete for P", SIGACT News 7 (1975), 18-20. -/
public theorem_wanted succinct_circuit_value_exp_complete :
    succinctCircuitValueDec ∈ EXP ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ EXP → Cslib.CookLevin.PolyManyOneRed L succinctCircuitValueDec

end MetaMathlibExt.Complexity.KeyTheorems.SuccinctCircuitValueEXPComplete
