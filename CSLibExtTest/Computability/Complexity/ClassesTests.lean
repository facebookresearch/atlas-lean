/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Analysis.Matrix.PosDef

/-! Tests for the shared complexity-class definitions: executable circuit
evaluation and depth, the capped oracle evaluator, the capped interactive-proof
game, and the parity / majority decision problems, plus the quantum-circuit
API (`RatEnc`, `qBit`, `setBits`, `basisState`, `tensorProd`, `zeroState`,
`sqNorm`, `acceptProb`, gate application) and the bounded-fan-in invariant
`IsFanInLeTwo` of the `NC` definition. -/

namespace Cslib.Complexity.Classes

open scoped ComplexOrder

/-! ### Flat circuits -/

/-- AND of two inputs: `[x₀, x₁, x₀ ∧ x₁]` with `x₀ = true, x₁ = false`. -/
example : circuitEval
    ([ACGate.var ⟨0, by decide⟩, ACGate.var ⟨1, by decide⟩,
      ACGate.andGate [0, 1]] : List (ACGate 2))
    (fun i : Fin 2 => decide (i.val = 0)) = [true, false, false] := rfl

/-- A `mod 2` gate over two true inputs: `2 % 2 = 0`, so it outputs `true`. -/
example : circuitEval
    ([ACGate.var ⟨0, by decide⟩, ACGate.var ⟨1, by decide⟩,
      ACGate.modGate 2 [0, 1]] : List (ACGate 2))
    (fun _ => true) = [true, true, true] := rfl

/-- A `mod 0` gate outputs `false` by definition. -/
example : gateValue [true] (fun _ => true)
    (ACGate.modGate 0 [0] : ACGate 1) = false := rfl

/-- Depths of the AND circuit: inputs at depth 0, the AND gate at depth 1. -/
example : circuitDepths
    ([ACGate.var ⟨0, by decide⟩, ACGate.var ⟨1, by decide⟩,
      ACGate.andGate [0, 1]] : List (ACGate 2)) = [0, 0, 1] := rfl

/-- Depth of the AND circuit is 1. -/
example : circuitDepth
    ([ACGate.var ⟨0, by decide⟩, ACGate.var ⟨1, by decide⟩,
      ACGate.andGate [0, 1]] : List (ACGate 2)) = 1 := rfl

/-- `gateInputs` of an AND gate is its input list. -/
example : gateInputs (ACGate.andGate [0, 1] : ACGate 2) = [0, 1] := rfl

/-! ### Serial `(kind, refs)` circuit encoding -/

/-- Serializing a var gate gives kind `0` with the variable index. -/
example : acGateToPair (ACGate.var ⟨1, by decide⟩ : ACGate 2) = (0, [1]) := rfl

/-- Serializing a constant gives kind `1` with `1` for `true`, `0` for `false`. -/
example : acGateToPair (ACGate.const true : ACGate 2) = (1, [1]) := rfl

/-- Serializing a NOT gate gives kind `2` with its predecessor. -/
example : acGateToPair (ACGate.notGate 0 : ACGate 2) = (2, [0]) := rfl

/-- Serializing AND/OR gates gives kinds `3`/`4` with the predecessor list. -/
example : acGateToPair (ACGate.andGate [0, 1] : ACGate 2) = (3, [0, 1]) := rfl

/-- Serializing an OR gate gives kind `4` with the predecessor list. -/
example : acGateToPair (ACGate.orGate [0, 1] : ACGate 2) = (4, [0, 1]) := rfl

/-- Serializing a `mod` gate is lossy: it becomes the all-false kind `5`. -/
example : acGateToPair (ACGate.modGate 2 [0, 1] : ACGate 2) = (5, []) := rfl

/-- Decoding `(0, [1])` recovers the var gate. -/
example : acGateOfPair (n := 2) (0, [1]) = ACGate.var ⟨1, by decide⟩ := rfl

/-- Decoding `(1, [1])` recovers `const true`; `(1, [0])` recovers `const false`. -/
example : acGateOfPair (n := 2) (1, [1]) = ACGate.const true := rfl

/-- Decoding `(1, [0])` recovers `const false`. -/
example : acGateOfPair (n := 2) (1, [0]) = ACGate.const false := rfl

/-- Decoding `(2, [0])` recovers the NOT gate. -/
example : acGateOfPair (n := 2) (2, [0]) = ACGate.notGate 0 := rfl

/-- Decoding `(3, [0, 1])` recovers the AND gate. -/
example : acGateOfPair (n := 2) (3, [0, 1]) = ACGate.andGate [0, 1] := rfl

/-- Decoding `(4, [0, 1])` recovers the OR gate. -/
example : acGateOfPair (n := 2) (4, [0, 1]) = ACGate.orGate [0, 1] := rfl

/-- Malformed pairs decode to `const false`: a var gate with the wrong
payload shape, an unknown kind, and a kind with a malformed payload. -/
example : acGateOfPair (n := 2) (0, [1, 2]) = ACGate.const false := rfl

/-- An unknown kind decodes to `const false`. -/
example : acGateOfPair (n := 2) (7, [0]) = ACGate.const false := rfl

/-- Kind `5` (the lossy `mod` serialization) decodes to `const false`. -/
example : acGateOfPair (n := 2) (5, []) = ACGate.const false := rfl

/-- An out-of-range input index (`i = 5` with `n = 2`) decodes to
`const false`, matching the serial evaluator's `false` for missing inputs. -/
example : acGateOfPair (n := 2) (0, [5]) = ACGate.const false := rfl

/-- At `n = 0` there are no input variables, so a var gate decodes to
`const false`. -/
example : acGateOfPair (n := 0) (0, [0]) = ACGate.const false := rfl

/-- Round-trip: serializing then decoding a var/const/NOT/AND/OR gate
recovers it (with `n = 2`). -/
example : acGateOfPair (n := 2) (acGateToPair (ACGate.var ⟨1, by decide⟩ : ACGate 2)) =
    ACGate.var ⟨1, by decide⟩ := rfl

/-- Round-trip for the AND gate. -/
example : acGateOfPair (n := 2) (acGateToPair (ACGate.andGate [0, 1] : ACGate 2)) =
    ACGate.andGate [0, 1] := rfl

/-- Round-trip is *not* the identity for `mod` gates: serialization is
lossy, so decoding gives `const false`, not the original gate. -/
example : acGateOfPair (n := 2) (acGateToPair (ACGate.modGate 2 [0, 1] : ACGate 2)) =
    ACGate.const false := rfl

/-- Serial evaluation of an out-of-range var gate is `false`. -/
example : serialGateEval [true, false] (fun i : Fin 2 => decide (i.val = 0))
    (0, [5]) = false := rfl

/-- Serial evaluation of an unknown kind is `false`. -/
example : serialGateEval [true, false] (fun i : Fin 2 => decide (i.val = 0))
    (7, [0]) = false := rfl

/-- Serial evaluation agrees with the typed evaluator on a decoded AND gate:
`gateValue` of the decoded gate is `true ∧ false = false`. -/
example : serialGateEval [true, false] (fun i : Fin 2 => decide (i.val = 0))
    (3, [0, 1]) =
    gateValue [true, false] (fun i : Fin 2 => decide (i.val = 0))
      (acGateOfPair (n := 2) (3, [0, 1])) := rfl

/-- `gateValue_ofPair` on a concrete out-of-range var gate: both sides `false`. -/
example : serialGateEval [true, false] (fun i : Fin 2 => decide (i.val = 0))
    (0, [5]) =
    gateValue [true, false] (fun i : Fin 2 => decide (i.val = 0))
      (acGateOfPair (n := 2) (0, [5])) := by
  exact gateValue_ofPair [true, false] (fun i : Fin 2 => decide (i.val = 0)) (0, [5])

/-! ### Capped oracle evaluation -/

/-- With empty queries and a constant-`true` final decision, the oracle
machine accepts. -/
example : evalOracle 10 (fun _ => []) (fun _ => true) (fun _ => false) [] 3 [] =
    true := rfl

/-- A query longer than the cap halts the machine early with `final`,
so the history stays empty. -/
example : evalOracle 10 (fun _ => List.replicate 11 true)
    (fun p => decide (p.2 = [])) (fun _ => false) [] 3 [] = true := rfl

/-- With a large enough cap the same query is asked and the history is
nonempty, so the final decision differs. -/
example : evalOracle 20 (fun _ => List.replicate 11 true)
    (fun p => decide (p.2 = [])) (fun _ => false) [] 3 [] = false := rfl

/-! ### Capped interactive-proof games -/

/-- Zero rounds: the game is just the verifier's decision. -/
example : IPGame 10 (fun _ => []) (fun _ => true) (fun _ => []) [] [] 0 [] =
    true := rfl

/-- A verifier message longer than the cap rejects. -/
example : IPGame 10 (fun _ => List.replicate 11 true) (fun _ => true)
    (fun _ => []) [] [] 1 [] = false := rfl

/-- With a large enough cap the same message goes through and the verifier
decides `true`. -/
example : IPGame 20 (fun _ => List.replicate 11 true) (fun _ => true)
    (fun _ => []) [] [] 1 [] = true := rfl

/-! ### Parity and majority -/

/-- Two `true` bits: even parity. -/
example : parityDec [true, false, true] = false := rfl

/-- One `true` bit: odd parity. -/
example : parityDec [true] = true := rfl

/-- Two of three bits `true`: majority. -/
example : majorityDec [true, true, false] = true := rfl

/-- One of two bits `true`: no strict majority. -/
example : majorityDec [true, false] = false := rfl

/-! ### Bounded fan-in (`IsFanInLeTwo`) -/

/-- An AND gate with exactly two predecessors is fan-in `≤ 2`. -/
example : IsFanInLeTwo ([ACGate.andGate [0, 1]] : List (ACGate 2)) := by
  intro g hg
  simp at hg
  subst hg
  exact le_rfl

/-- An AND gate with one predecessor is fan-in `≤ 2`. -/
example : IsFanInLeTwo ([ACGate.andGate [0]] : List (ACGate 2)) := by
  intro g hg
  simp at hg
  subst hg
  decide

/-- An AND gate with no predecessors is fan-in `≤ 2`. -/
example : IsFanInLeTwo ([ACGate.andGate []] : List (ACGate 2)) := by
  intro g hg
  simp at hg
  subst hg
  decide

/-- An AND gate with three predecessors violates fan-in `≤ 2`. -/
example : ¬ IsFanInLeTwo ([ACGate.andGate [0, 1, 2]] : List (ACGate 3)) := by
  intro h
  have hh := h (ACGate.andGate [0, 1, 2]) (by simp)
  exact absurd hh (by decide)

/-- An OR gate with three predecessors violates fan-in `≤ 2`. -/
example : ¬ IsFanInLeTwo ([ACGate.orGate [0, 1, 2]] : List (ACGate 3)) := by
  intro h
  have hh := h (ACGate.orGate [0, 1, 2]) (by simp)
  exact absurd hh (by decide)

/-- A `mod` gate with three predecessors violates fan-in `≤ 2`. -/
example : ¬ IsFanInLeTwo ([ACGate.modGate 2 [0, 1, 2]] : List (ACGate 3)) := by
  intro h
  have hh := h (ACGate.modGate 2 [0, 1, 2]) (by simp)
  exact absurd hh (by decide)

/-- `var`/`const`/`not` gates always satisfy fan-in `≤ 2`. -/
example : IsFanInLeTwo ([ACGate.var ⟨0, by decide⟩, ACGate.const true,
    ACGate.notGate 0] : List (ACGate 2)) := by
  intro g hg
  simp at hg
  rcases hg with rfl | rfl | rfl <;> trivial

/-! ### Quantum-circuit API -/

/-- `toRat`: `(sign, numerator, denominator)` with `false` for positive. -/
example : toRat (false, 1, 2) = 1 / 2 := by norm_num [toRat]

/-- `toRat`: `true` for negative. -/
example : toRat (true, 1, 2) = -1 / 2 := by norm_num [toRat]

/-- `toComplex`: real and imaginary parts from two rational encodings. -/
example : toComplex ((false, 1, 1), (true, 1, 1)) = ⟨1, -1⟩ := by
  exact Complex.ext (by simp [toComplex, toRat]) (by simp [toComplex, toRat])

/-- `qIdx2`: row-major enumeration of `Fin 2 × Fin 2`. -/
example : qIdx2 (⟨0, by decide⟩, ⟨0, by decide⟩) = 0 := rfl

/-- `qIdx2 (0, 1) = 1`. -/
example : qIdx2 (⟨0, by decide⟩, ⟨1, by decide⟩) = 1 := rfl

/-- `qIdx2 (1, 0) = 2`. -/
example : qIdx2 (⟨1, by decide⟩, ⟨0, by decide⟩) = 2 := rfl

/-- `qIdx2 (1, 1) = 3`. -/
example : qIdx2 (⟨1, by decide⟩, ⟨1, by decide⟩) = 3 := rfl

/-- `qBit`: bits of `5 = 101₂`, least significant first. -/
example : qBit 0 5 = 1 := rfl

/-- `qBit 1 5 = 0`. -/
example : qBit 1 5 = 0 := rfl

/-- `qBit 2 5 = 1`. -/
example : qBit 2 5 = 1 := rfl

/-- `qBit` beyond the highest set bit is `0`. -/
example : qBit 3 5 = 0 := rfl

/-- `qBit 0 0 = 0`. -/
example : qBit 0 0 = 0 := rfl

/-- `qNumOf`: `[true, false, true]` is `1 + 0 + 4 = 5`, least significant first. -/
example : qNumOf [true, false, true] = 5 := rfl

/-- `qNumOf [false, true] = 2`. -/
example : qNumOf [false, true] = 2 := rfl

/-- `basisState`: supported exactly on the index of the input bitstring. -/
example : basisState [true, false, true] ⟨5, by decide⟩ = 1 := rfl

/-- `basisState` vanishes off its index. -/
example : basisState [true, false, true] ⟨4, by decide⟩ = 0 := rfl

/-- `zeroState`: supported exactly on index `0`. -/
example : zeroState 2 ⟨0, by decide⟩ = 1 := rfl

/-- `zeroState` vanishes off index `0`. -/
example : zeroState 2 ⟨1, by decide⟩ = 0 := rfl

/-- `setBits`: replacing bits `(1, 1)` of `5 = 101₂` (qubits `0`, `2`) by
`(0, 0)` gives `0`. -/
example : (setBits 3 5 0 2 (0, 0)).val = 0 := rfl

/-- `setBits`: replacing by `(1, 1)` leaves `5` unchanged. -/
example : (setBits 3 5 0 2 (1, 1)).val = 5 := rfl

/-- `setBits`: replacing by `(0, 1)` clears qubit `0`, giving `4`. -/
example : (setBits 3 5 0 2 (0, 1)).val = 4 := rfl

/-- `setBits`: replacing by `(1, 0)` clears qubit `2`, giving `1`. -/
example : (setBits 3 5 0 2 (1, 0)).val = 1 := rfl

/-- `tensorProd` of `|1⟩` and `|0⟩`: supported on combined index `1`
(`s % 2 = 1`, `s / 2 = 0`), value `1`. -/
example : tensorProd (basisState [true]) (basisState [false]) ⟨1, by decide⟩ = 1 := by
  simp only [tensorProd, basisState, qNumOf]
  norm_num

/-- `tensorProd` of `|1⟩` and `|0⟩` vanishes at combined index `2`
(`s % 2 = 0`, the first factor's index `0 ≠ 1`). -/
example : tensorProd (basisState [true]) (basisState [false]) ⟨2, by decide⟩ = 0 := by
  simp only [tensorProd, basisState, qNumOf]
  norm_num

/-- The squared norm of a basis state is `1`. -/
example : sqNorm (basisState [true, false]) = 1 := by
  show (∑ s : Fin (2 ^ 2),
    (starRingEnd ℂ (basisState [true, false] s) * basisState [true, false] s).re) = 1
  rw [Finset.sum_eq_single ⟨1, by decide⟩]
  · simp [basisState, qNumOf]
  · intro s _ hs
    have h0 : basisState [true, false] s = 0 := by
      simp only [basisState]
      split_ifs with h
      · exfalso
        apply hs
        exact Fin.ext h
      · rfl
    rw [h0]
    simp
  · simp

/-- `acceptProb` of `|1⟩` is `1` (qubit `0` measures `1`). -/
example : acceptProb (basisState [true]) = 1 := by
  show (∑ s : Fin (2 ^ 1), if qBit 0 s.val = 1 then
    (starRingEnd ℂ (basisState [true] s) * basisState [true] s).re else 0) = 1
  rw [Finset.sum_eq_single ⟨1, by decide⟩]
  · simp [basisState, qNumOf, qBit]
  · intro s _ hs
    by_cases hq : qBit 0 s.val = 1
    · have hs1 : s = ⟨1, by decide⟩ := by
        fin_cases s <;> simp [qBit] at hq ⊢
      exact absurd hs1 hs
    · simp [hq]
  · simp

/-- `acceptProb` of `|0⟩` is `0` (qubit `0` measures `0`). -/
example : acceptProb (basisState [false]) = 0 := by
  show (∑ s : Fin (2 ^ 1), if qBit 0 s.val = 1 then
    (starRingEnd ℂ (basisState [false] s) * basisState [false] s).re else 0) = 0
  rw [Finset.sum_eq_zero]
  intro s _
  by_cases hq : qBit 0 s.val = 1
  · have hs1 : s = ⟨1, by decide⟩ := by
      fin_cases s <;> simp [qBit] at hq ⊢
    rw [hs1]
    simp [basisState, qNumOf]
  · simp [hq]

/-- The identity `4 × 4` gate, row-major: `1` on the diagonal, `0` elsewhere. -/
def identEntries : List (RatEnc × RatEnc) :=
  List.ofFn (fun i : Fin 16 =>
    if i.val % 5 = 0 then ((false, 1, 1), (false, 0, 1))
    else ((false, 0, 1), (false, 0, 1)))

/-- `matrixOfEntries` of the identity entries: diagonal entry `(0,0),(0,0)` is `1`. -/
example : (matrixOfEntries identEntries) (⟨0, by decide⟩, ⟨0, by decide⟩)
    (⟨0, by decide⟩, ⟨0, by decide⟩) = 1 := by
  show toComplex (identEntries.getD 0 _) = 1
  have h : identEntries.getD 0 ((false, 0, 1), (false, 0, 1)) =
      ((false, 1, 1), (false, 0, 1)) := rfl
  rw [h]
  exact Complex.ext (by simp [toComplex, toRat]) (by simp [toComplex, toRat])

/-- `matrixOfEntries` of the identity entries: off-diagonal entry is `0`. -/
example : (matrixOfEntries identEntries) (⟨1, by decide⟩, ⟨0, by decide⟩)
    (⟨0, by decide⟩, ⟨0, by decide⟩) = 0 := by
  show toComplex (identEntries.getD 8 _) = 0
  have h : identEntries.getD 8 ((false, 0, 1), (false, 0, 1)) =
      ((false, 0, 1), (false, 0, 1)) := rfl
  rw [h]
  exact Complex.ext (by simp [toComplex, toRat]) (by simp [toComplex, toRat])

/-- Applying the identity gate to `|00⟩` leaves amplitude `1` at index `0`. -/
example : applyGate 2 (0, 1, identEntries) (basisState [false, false])
    ⟨0, by decide⟩ = 1 := by
  show (∑ b : Fin 2 × Fin 2,
    (matrixOfEntries identEntries) (qBit 0 0, qBit 1 0) b *
      basisState [false, false] (setBits 2 0 0 1 b)) = 1
  rw [Finset.sum_eq_single (0, 0)]
  · have h1 : (matrixOfEntries identEntries) (qBit 0 0, qBit 1 0) (0, 0) = 1 := by
      show toComplex (identEntries.getD 0 _) = 1
      have h : identEntries.getD 0 ((false, 0, 1), (false, 0, 1)) =
          ((false, 1, 1), (false, 0, 1)) := rfl
      rw [h]
      exact Complex.ext (by simp [toComplex, toRat]) (by simp [toComplex, toRat])
    have h2 : setBits 2 0 0 1 (0, 0) = (⟨0, by decide⟩ : Fin (2 ^ 2)) := rfl
    rw [h2, h1]
    simp [basisState, qNumOf]
  · intro b _ hb
    have hne : setBits 2 0 0 1 b ≠ (⟨0, by decide⟩ : Fin (2 ^ 2)) := by
      intro h
      exact hb (by
        have hiff : setBits 2 0 0 1 b = ⟨0, by decide⟩ ↔ b = (0, 0) := by
          fin_cases b <;> decide
        exact hiff.mp h)
    have hpsi : basisState [false, false] (setBits 2 0 0 1 b) = 0 := by
      simp only [basisState]
      split_ifs with h
      · exact absurd (Fin.ext h) hne
      · rfl
    rw [hpsi, mul_zero]
  · simp

/-- The Pauli-X gate on qubit `0` (qubit `1` untouched), row-major:
entry `(out, in)` is `1` iff `out₀ = 1 - in₀` and `out₁ = in₁`. -/
def xGateEntries : List (RatEnc × RatEnc) :=
  List.ofFn (fun i : Fin 16 =>
    let out := i.val / 4
    let inp := i.val % 4
    if out / 2 = 1 - inp / 2 ∧ out % 2 = inp % 2 then
      ((false, 1, 1), (false, 0, 1))
    else ((false, 0, 1), (false, 0, 1)))

/-- `matrixOfEntries` of the `X` entries: `((1,0),(0,0))` is `1` (flips qubit `0`). -/
example : (matrixOfEntries xGateEntries) (⟨1, by decide⟩, ⟨0, by decide⟩)
    (⟨0, by decide⟩, ⟨0, by decide⟩) = 1 := by
  show toComplex (xGateEntries.getD 8 _) = 1
  have h : xGateEntries.getD 8 ((false, 0, 1), (false, 0, 1)) =
      ((false, 1, 1), (false, 0, 1)) := rfl
  rw [h]
  exact Complex.ext (by simp [toComplex, toRat]) (by simp [toComplex, toRat])

/-- `matrixOfEntries` of the `X` entries: `((1,0),(1,0))` is `0` (no fixed point). -/
example : (matrixOfEntries xGateEntries) (⟨1, by decide⟩, ⟨0, by decide⟩)
    (⟨1, by decide⟩, ⟨0, by decide⟩) = 0 := by
  show toComplex (xGateEntries.getD 10 _) = 0
  have h : xGateEntries.getD 10 ((false, 0, 1), (false, 0, 1)) =
      ((false, 0, 1), (false, 0, 1)) := rfl
  rw [h]
  exact Complex.ext (by simp [toComplex, toRat]) (by simp [toComplex, toRat])

/-- Applying the `X` gate on qubit `0` to `|00⟩` gives amplitude `1` at index `1`
(`|10⟩`, qubit `0` flipped). -/
example : applyGate 2 (0, 1, xGateEntries) (basisState [false, false])
    ⟨1, by decide⟩ = 1 := by
  show (∑ b : Fin 2 × Fin 2,
    (matrixOfEntries xGateEntries) (qBit 0 1, qBit 1 1) b *
      basisState [false, false] (setBits 2 1 0 1 b)) = 1
  rw [Finset.sum_eq_single (0, 0)]
  · have h1 : (matrixOfEntries xGateEntries) (qBit 0 1, qBit 1 1) (0, 0) = 1 := by
      show toComplex (xGateEntries.getD 8 _) = 1
      have h : xGateEntries.getD 8 ((false, 0, 1), (false, 0, 1)) =
          ((false, 1, 1), (false, 0, 1)) := rfl
      rw [h]
      exact Complex.ext (by simp [toComplex, toRat]) (by simp [toComplex, toRat])
    have h2 : setBits 2 1 0 1 (0, 0) = (⟨0, by decide⟩ : Fin (2 ^ 2)) := rfl
    rw [h2, h1]
    simp [basisState, qNumOf]
  · intro b _ hb
    have hne : setBits 2 1 0 1 b ≠ (⟨0, by decide⟩ : Fin (2 ^ 2)) := by
      intro h
      exact hb (by
        have hiff : setBits 2 1 0 1 b = ⟨0, by decide⟩ ↔ b = (0, 0) := by
          fin_cases b <;> decide
        exact hiff.mp h)
    have hpsi : basisState [false, false] (setBits 2 1 0 1 b) = 0 := by
      simp only [basisState]
      split_ifs with h
      · exact absurd (Fin.ext h) hne
      · rfl
    rw [hpsi, mul_zero]
  · simp

/-- `QGateWellFormed`: a gate addressing a qubit `≥ N` is not well-formed. -/
example : ¬ QGateWellFormed 2 (0, 5, []) := by
  intro h
  exact absurd h.2.1 (by decide)

/-- `QGateWellFormed`: a gate with `i ≥ j` is not well-formed. -/
example : ¬ QGateWellFormed 2 (3, 1, []) := by
  intro h
  exact absurd h.1 (by decide)

end Cslib.Complexity.Classes
