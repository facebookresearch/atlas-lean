/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.ACGateBridge

/-! Tests for the translation of flat `ACGate` circuits into CSLib circuits: a small circuit
evaluated both ways (`circuitEval` and `Circuit.eval` of `toCircuit`), the gate count of the
translation (input gates add no CSLib gate, `size_toCircuit`), depths without constants, the
depth offset of a constant gate and a constant that leaves the circuit depth unchanged, the exact
depths `acCircuitDepths`, zero-argument gates, a `mod` gate, a `mod` gate that reads one gate
twice, the empty circuit, and the characteristic lemmas of `acInterpretation`. -/

namespace Cslib.Complexity.Classes

open Cslib.Circuits

/-- `x₀ ∨ ¬(x₀ ∧ x₁)` as a flat circuit: two input gates, then AND, NOT and OR. -/
private def sample : List (ACGate 2) :=
  [.var 0, .var 1, .andGate [0, 1], .notGate 2, .orGate [0, 3]]

private theorem sample_wf : WellFormedCircuit sample := by
  unfold WellFormedCircuit
  decide

/-- The input `x₀ = true`, `x₁ = false`. -/
private def input : Fin 2 → Bool := fun i => decide (i.val = 0)

/-! ### Evaluation, both ways -/

/-- The flat values of all five gates. -/
example : circuitEval sample input = [true, false, false, true, true] := rfl

/-- The CSLib circuit computes the same five values. -/
example : List.ofFn ((toCircuit sample sample_wf).eval acInterpretation input) =
    [true, false, false, true, true] := by
  decide

/-- The last output computes `x₀ ∨ ¬(x₀ ∧ x₁)` on every input. -/
example : ∀ x : Fin 2 → Bool,
    (toCircuit sample sample_wf).eval acInterpretation x ⟨4, by decide⟩ =
      (x 0 || !(x 0 && x 1)) := by
  decide

/-- The evaluation theorem, instantiated. -/
example (x : Fin 2 → Bool) :
    List.ofFn ((toCircuit sample sample_wf).eval acInterpretation x) = circuitEval sample x :=
  ofFn_eval_toCircuit sample sample_wf x

/-! ### Size -/

/-- The two input gates become input wires: three CSLib gates for five flat gates. -/
example : (toCircuit sample sample_wf).size = 3 := rfl

/-- `size_toCircuit` counts the same three gates: the flat gates that are not input gates. -/
example : (toCircuit sample sample_wf).size = 3 := by
  rw [size_toCircuit]
  rfl

/-! ### Depth -/

/-- Without constant gates every output is exactly as deep as its flat gate. -/
example : List.ofFn (toCircuit sample sample_wf).outputDepths = circuitDepths sample := by
  decide

/-- Without constant gates the circuit depths agree, here both `3`. -/
example : (toCircuit sample sample_wf).depth = circuitDepth sample :=
  depth_toCircuit_eq sample sample_wf (by intro b; simp [sample])

example : circuitDepth sample = 3 := rfl

/-- A single constant gate. -/
private def oneConst : List (ACGate 0) := [.const true]

private theorem oneConst_wf : WellFormedCircuit oneConst := by
  unfold WellFormedCircuit
  decide

/-- The constant gate has flat depth `0` and CSLib depth `1`: the bound of `depth_toCircuit_le`
is attained. -/
example : circuitDepth oneConst = 0 ∧ (toCircuit oneConst oneConst_wf).depth = 1 := by
  decide

/-- A constant gate feeding an AND gate. -/
private def constAnd : List (ACGate 1) := [.var 0, .const false, .andGate [0, 1]]

private theorem constAnd_wf : WellFormedCircuit constAnd := by
  unfold WellFormedCircuit
  decide

/-- The constant shifts the AND gate as well: flat depths `[0, 0, 1]`, CSLib output depths
`[0, 1, 2]`. -/
example : circuitDepths constAnd = [0, 0, 1] ∧
    List.ofFn (toCircuit constAnd constAnd_wf).outputDepths = [0, 1, 2] := by
  decide

/-- A constant gate off the deepest path. -/
private def constAside : List (ACGate 1) := [.const true, .var 0, .notGate 1, .notGate 2]

private theorem constAside_wf : WellFormedCircuit constAside := by
  unfold WellFormedCircuit
  decide

/-- The constant gate is one level deeper in CSLib, but both circuit depths are `2`: a constant
gate does not always raise the circuit depth. -/
example : List.ofFn (toCircuit constAside constAside_wf).outputDepths = [1, 0, 1, 2] ∧
    circuitDepths constAside = [0, 0, 1, 2] ∧
    (toCircuit constAside constAside_wf).depth = circuitDepth constAside := by
  decide

/-- `acCircuitDepths` gives the CSLib output depths exactly, constants included: `[0, 1, 2]` for
`constAnd`, where `circuitDepths` gives `[0, 0, 1]`. -/
example : List.ofFn (toCircuit constAnd constAnd_wf).outputDepths = [0, 1, 2] := by
  rw [ofFn_outputDepths_toCircuit]
  decide

/-- `depth_toCircuit` gives depth `1` for the one constant gate. -/
example : (toCircuit oneConst oneConst_wf).depth = 1 := by
  rw [depth_toCircuit]
  rfl

/-- Off the deepest path the constant gate still has depth `1`, and the circuit depth is the
largest entry, `2`. -/
example : acCircuitDepths constAside = [1, 0, 1, 2] ∧
    (toCircuit constAside constAside_wf).depth = 2 := by
  rw [depth_toCircuit]
  decide

/-! ### Degenerate cases -/

/-- Zero-argument gates: AND, OR, `mod 0` and `mod 3`. -/
private def nullary : List (ACGate 0) := [.andGate [], .orGate [], .modGate 0 [], .modGate 3 []]

private theorem nullary_wf : WellFormedCircuit nullary := by
  unfold WellFormedCircuit
  decide

/-- AND gives `true`, OR gives `false`, `mod 0` gives `false` and `mod 3` gives `true` (zero
`true` arguments), in both models. -/
example : circuitEval nullary Fin.elim0 = [true, false, false, true] ∧
    List.ofFn ((toCircuit nullary nullary_wf).eval acInterpretation Fin.elim0) =
      [true, false, false, true] := by
  decide

/-- Every zero-argument gate has depth `1` in both models. -/
example : circuitDepths nullary = [1, 1, 1, 1] ∧
    List.ofFn (toCircuit nullary nullary_wf).outputDepths = [1, 1, 1, 1] := by
  decide

/-- A `mod 2` gate over two inputs. -/
private def modTwo : List (ACGate 2) := [.var 0, .var 1, .modGate 2 [0, 1]]

private theorem modTwo_wf : WellFormedCircuit modTwo := by
  unfold WellFormedCircuit
  decide

/-- Both models agree on the `mod 2` gate on every input. -/
example : ∀ x : Fin 2 → Bool,
    List.ofFn ((toCircuit modTwo modTwo_wf).eval acInterpretation x) = circuitEval modTwo x := by
  decide

/-- The empty flat circuit gives a circuit with no gate, no output and depth `0`. -/
example (h : WellFormedCircuit ([] : List (ACGate 0))) :
    (toCircuit [] h).size = 0 ∧ (toCircuit [] h).depth = 0 :=
  ⟨rfl, rfl⟩

/-! ### Repeated references -/

/-- A `mod 2` gate that reads input gate `0` twice, after a constant feeding an AND gate, and
followed by a `mod 0` gate with one argument and zero-argument AND and OR gates. -/
private def repeatedRef : List (ACGate 2) :=
  [.var 0, .var 1, .const true, .notGate 1, .andGate [0, 2, 3],
    .orGate [1, 4], .modGate 2 [0, 0, 1], .modGate 0 [0], .andGate [], .orGate []]

private theorem repeatedRef_wf : WellFormedCircuit repeatedRef := by
  unfold WellFormedCircuit
  decide

/-- On `x₀ = true`, `x₁ = false` the `mod 2` gate (gate `6`) counts gate `0` twice: two `true`
arguments, so it outputs `true`. The CSLib circuit gives the flat values
(`ofFn_eval_toCircuit`). -/
example : List.ofFn ((toCircuit repeatedRef repeatedRef_wf).eval acInterpretation input) =
    [true, false, true, true, true, true, true, false, true, false] := by
  rw [ofFn_eval_toCircuit]
  decide

/-- Counted twice, `x₀` never changes the parity: on every input the `mod 2` gate of the CSLib
circuit computes `¬x₁`. -/
example : ∀ x : Fin 2 → Bool,
    (toCircuit repeatedRef repeatedRef_wf).eval acInterpretation x ⟨6, by decide⟩ = !x 1 := by
  decide

/-- Eight CSLib gates for ten flat gates: the two input gates add none. -/
example : (toCircuit repeatedRef repeatedRef_wf).size = 8 := by
  rw [size_toCircuit]
  rfl

/-- The constant (gate `2`) feeds the AND gate (gate `4`), whose other input gate `3` already has
depth `1`, so the AND gate keeps depth `2`: `acCircuitDepths` and `circuitDepths` differ only at
the constant, and the circuit depth is `3`. -/
example : acCircuitDepths repeatedRef = [0, 0, 1, 1, 2, 3, 1, 1, 1, 1] ∧
    circuitDepths repeatedRef = [0, 0, 0, 1, 2, 3, 1, 1, 1, 1] ∧
    (toCircuit repeatedRef repeatedRef_wf).depth = 3 := by
  rw [depth_toCircuit]
  decide

/-! ### The interpretation -/

example (f : Fin 3 → Bool) : acInterpretation (.and 3) f = decide (∀ i, f i = true) :=
  acInterpretation_and 3 f

example : acInterpretation (.or 0) Fin.elim0 = false := by
  simp [acInterpretation_or]

/-- Two of three arguments are `true`, and `2` divides `2`. -/
example : acInterpretation (.mod 2 3) (fun i => decide (i.val < 2)) = true := by
  rw [acInterpretation_mod]
  decide

end Cslib.Complexity.Classes
