/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Circuit.Basic
public import Init.Data.BitVec.Bitblast

/-!
# The ripple-carry adder as a CSLib circuit

The ripple-carry adder (Cormen, Leiserson and Rivest, *Introduction to Algorithms*, first edition
(1990), Section 29.2.1, "Ripple-carry addition"; Harris and Harris, *Digital Design and Computer
Architecture*, second edition (2012), Section 5.2.1) adds two `n`-bit numbers with a chain of full
adders.
Bit `i` combines `a = x_i`, `b = y_i` and the incoming carry `c_i` with five two-input gates,

  `g₀ = a ⊕ b`, `s_i = g₀ ⊕ c_i`, `g₂ = a ∧ b`, `g₃ = g₀ ∧ c_i`, `c_{i+1} = g₂ ∨ g₃`,

and passes `c_{i+1}` to bit `i + 1`. Here the adder is a circuit over CSLib's straight-line circuit
model (`Cslib.Circuits.Circuit`) with the basis `arithSignature` of binary XOR, AND and OR gates
(`arithInterpretation`). `rippleCarryAdder n` has `2 n + 1` inputs (the bits of `x`, the bits of
`y`, the carry in; `rcaInput`), `5 n` gates, and `n + 1` outputs (the sum bits, then the carry
out). Main results:

* `rippleCarryAdder_sum`, `rippleCarryAdder_carry`: on the bits of `x y : BitVec n` and a carry
  `c`, the outputs are the bits of `(BitVec.adc x y c).2 = x + y + c` and the carry out
  `(BitVec.adc x y c).1`, Lean core's specification of addition with carry.
* `rippleCarryAdder_size`: `5 n` gates.

The proof identifies every gate's value (`rcaProgram_eval`): gate `5 i + 4` carries
`BitVec.carry (i + 1) x y c`, the carry function of Lean's bit-blasting of addition, and the
recurrence `BitVec.carry_succ` matches the full adder's carry gate.

## Cost model

Circuit size (`Circuit.size`, the gate count) is the cost measure; inputs and output designation
are free, as in CSLib's circuit model.
-/

@[expose] public section

namespace Cslib.Circuits

/-- Binary gates for arithmetic circuits: XOR, AND and OR. -/
inductive ArithGate where
  | xor
  | and
  | or
  deriving Repr, DecidableEq

/-- The arithmetic basis: three binary gates. -/
def arithSignature : Signature where
  Op := ArithGate
  Arity _ := 2

/-- The Boolean meaning of the arithmetic gates. -/
def arithInterpretation : Interpretation arithSignature Bool
  | .xor, f => f ⟨0, by decide⟩ ^^ f ⟨1, by decide⟩
  | .and, f => f ⟨0, by decide⟩ && f ⟨1, by decide⟩
  | .or, f => f ⟨0, by decide⟩ || f ⟨1, by decide⟩

@[simp] theorem arithInterpretation_xor (f : Fin 2 → Bool) :
    arithInterpretation .xor f = (f 0 ^^ f 1) := rfl

@[simp] theorem arithInterpretation_and (f : Fin 2 → Bool) :
    arithInterpretation .and f = (f 0 && f 1) := rfl

@[simp] theorem arithInterpretation_or (f : Fin 2 → Bool) :
    arithInterpretation .or f = (f 0 || f 1) := rfl

/-- A binary gate reading the wires `u` and `v`. -/
def binLine {m g : ℕ} (op : ArithGate) (u v : Wire m g) : Line arithSignature m g :=
  ⟨op, fun k => if k.val = 0 then u else v⟩

theorem binLine_eval {m g : ℕ} (op : ArithGate) (u v : Wire m g) (x : Fin m → Bool)
    (gates : Fin g → Bool) :
    (binLine op u v).eval arithInterpretation x gates =
      arithInterpretation op fun k =>
        if k.val = 0 then Wire.elim x gates u else Wire.elim x gates v := by
  simp only [Line.eval, binLine]
  congr 1
  funext k
  simp only [Function.comp_apply]
  split_ifs <;> rfl

namespace RippleCarry

/-- The carry into bit `i`, as a wire at gate count `g ≥ 5 i`: the carry-in input for bit `0`,
otherwise the carry-out gate `5 i - 1` of bit `i - 1`. -/
def carryWire (n g i : ℕ) (hi : 5 * i ≤ g) : Wire (2 * n + 1) g :=
  if h : i = 0 then Wire.input ⟨2 * n, by omega⟩ else Wire.gate ⟨5 * i - 1, by omega⟩

/-- Gate `g` of the adder: role `g % 5` of the full adder for bit `g / 5`. -/
def line (n g : ℕ) (hg : g < 5 * n) : Line arithSignature (2 * n + 1) g :=
  let a : Wire (2 * n + 1) g := Wire.input ⟨g / 5, by omega⟩
  let b : Wire (2 * n + 1) g := Wire.input ⟨n + g / 5, by omega⟩
  let c := carryWire n g (g / 5) (Nat.mul_div_le g 5)
  if h0 : g % 5 = 0 then binLine .xor a b
  else if h1 : g % 5 = 1 then binLine .xor (Wire.gate ⟨g - 1, by omega⟩) c
  else if h2 : g % 5 = 2 then binLine .and a b
  else if h3 : g % 5 = 3 then binLine .and (Wire.gate ⟨g - 3, by omega⟩) c
  else binLine .or (Wire.gate ⟨g - 2, by omega⟩) (Wire.gate ⟨g - 1, by omega⟩)

end RippleCarry

open RippleCarry

/-- The first `g` gates of the `n`-bit adder. -/
def rcaProgram (n : ℕ) : (g : ℕ) → g ≤ 5 * n → Program arithSignature (2 * n + 1) g
  | 0, _ => .empty
  | g + 1, h => (rcaProgram n g (by omega)).gate (line n g (by omega))

/-- The `n`-bit ripple-carry adder: `2 n + 1` inputs, `5 n` gates, outputs the `n` sum bits and
the carry out. -/
def rippleCarryAdder (n : ℕ) : Circuit arithSignature (2 * n + 1) (n + 1) where
  size := 5 * n
  program := rcaProgram n (5 * n) (Nat.le_refl _)
  outputs o := if h : o.val < n then Wire.gate ⟨5 * o.val + 1, by omega⟩
    else carryWire n (5 * n) n (Nat.le_refl _)

/-- The adder's input: the bits of `x`, the bits of `y`, then the carry in. -/
def rcaInput {n : ℕ} (x y : BitVec n) (c : Bool) : Fin (2 * n + 1) → Bool := fun j =>
  if j.val < n then x.getLsbD j.val else if j.val < 2 * n then y.getLsbD (j.val - n) else c

/-- The value of gate `j`: role `j % 5` of the full adder for bit `i = j / 5`. -/
def rcaSpec {n : ℕ} (x y : BitVec n) (c : Bool) (j : ℕ) : Bool :=
  let i := j / 5
  if j % 5 = 0 then x.getLsbD i ^^ y.getLsbD i
  else if j % 5 = 1 then (x.getLsbD i ^^ y.getLsbD i) ^^ BitVec.carry i x y c
  else if j % 5 = 2 then x.getLsbD i && y.getLsbD i
  else if j % 5 = 3 then (x.getLsbD i ^^ y.getLsbD i) && BitVec.carry i x y c
  else BitVec.carry (i + 1) x y c

theorem rcaSpec_carry {n : ℕ} (x y : BitVec n) (c : Bool) {i : ℕ} (hi : i ≠ 0) :
    rcaSpec x y c (5 * i - 1) = BitVec.carry i x y c := by
  have h4 : (5 * i - 1) % 5 = 4 := by omega
  have hd : (5 * i - 1) / 5 + 1 = i := by omega
  simp only [rcaSpec, h4, hd]
  simp

variable {n : ℕ} (x y : BitVec n) (c : Bool)

theorem rcaInput_a {i : ℕ} (hi : i < n) (h : i < 2 * n + 1) :
    rcaInput x y c ⟨i, h⟩ = x.getLsbD i := by
  simp [rcaInput, hi]

theorem rcaInput_b {i : ℕ} (hi : i < n) (h : n + i < 2 * n + 1) :
    rcaInput x y c ⟨n + i, h⟩ = y.getLsbD i := by
  have h1 : ¬ n + i < n := by omega
  have h2 : n + i < 2 * n := by omega
  simp only [rcaInput, h1, h2, ↓reduceIte]
  congr 1; omega

theorem rcaInput_c (h : 2 * n < 2 * n + 1) : rcaInput x y c ⟨2 * n, h⟩ = c := by
  have h1 : ¬ 2 * n < n := by omega
  have h2 : ¬ 2 * n < 2 * n := Nat.lt_irrefl _
  simp only [rcaInput, h1, h2, ↓reduceIte]

/-- The carry wire carries the carry. -/
theorem carryWire_value {g i : ℕ} (hi : 5 * i ≤ g) (gates : Fin g → Bool)
    (hgates : ∀ j (hj : j < g), gates ⟨j, hj⟩ = rcaSpec x y c j) :
    Wire.elim (rcaInput x y c) gates (carryWire n g i hi) = BitVec.carry i x y c := by
  unfold carryWire
  split_ifs with h
  · subst h
    simp only [Wire.elim_input]
    rw [rcaInput_c, BitVec.carry_zero]
  · simp only [Wire.elim_gate]
    rw [hgates, rcaSpec_carry x y c h]

/-- **Every gate's value**: gate `j` of the adder computes `rcaSpec x y c j`. -/
theorem rcaProgram_eval : ∀ (g : ℕ) (hg : g ≤ 5 * n) (j : ℕ) (hj : j < g),
    (rcaProgram n g hg).eval arithInterpretation (rcaInput x y c) ⟨j, hj⟩ = rcaSpec x y c j
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | g + 1, hg, j, hj => by
      have ih := rcaProgram_eval g (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
      · have : (⟨j, hj⟩ : Fin (g + 1)) = Fin.castSucc ⟨j, hj'⟩ := rfl
        rw [this, rcaProgram, Program.eval_gate_castSucc, ih]
      · have : (⟨j, hj⟩ : Fin (j + 1)) = Fin.last j := rfl
        rw [this, rcaProgram, Program.eval_gate_last]
        set prior := (rcaProgram n j (by omega)).eval arithInterpretation (rcaInput x y c)
        have hi : j / 5 < n := by omega
        have hA := rcaInput_a x y c hi (by omega)
        have hB := rcaInput_b x y c hi (by omega)
        have hC := carryWire_value x y c (Nat.mul_div_le j 5) prior ih
        unfold line
        split_ifs with h0 h1 h2 h3
        · rw [binLine_eval]
          simp only [Wire.elim_input, hA, hB, arithInterpretation, rcaSpec, h0]
          simp
        · rw [binLine_eval]
          simp only [Wire.elim_gate, arithInterpretation]
          rw [ih, hC]
          have e1 : (j - 1) % 5 = 0 := by omega
          have e2 : (j - 1) / 5 = j / 5 := by omega
          simp only [rcaSpec, e1, e2, h1]
          simp
        · rw [binLine_eval]
          simp only [Wire.elim_input, hA, hB, arithInterpretation, rcaSpec, h2]
          simp
        · rw [binLine_eval]
          simp only [Wire.elim_gate, arithInterpretation]
          rw [ih, hC]
          have e1 : (j - 3) % 5 = 0 := by omega
          have e2 : (j - 3) / 5 = j / 5 := by omega
          simp only [rcaSpec, e1, e2, h3]
          simp
        · have h4 : j % 5 = 4 := by omega
          rw [binLine_eval]
          simp only [Wire.elim_gate, arithInterpretation]
          rw [ih, ih]
          have e1 : (j - 2) % 5 = 2 := by omega
          have e2 : (j - 2) / 5 = j / 5 := by omega
          have e3 : (j - 1) % 5 = 3 := by omega
          have e4 : (j - 1) / 5 = j / 5 := by omega
          simp only [rcaSpec, e1, e2, e3, e4, h4, BitVec.carry_succ]
          cases x.getLsbD (j / 5) <;> cases y.getLsbD (j / 5) <;>
            cases BitVec.carry (j / 5) x y c <;> rfl

/-- **Sum bits**: output `i < n` is bit `i` of `(BitVec.adc x y c).2 = x + y + c`. -/
theorem rippleCarryAdder_sum (i : ℕ) (hi : i < n) :
    (rippleCarryAdder n).eval arithInterpretation (rcaInput x y c) ⟨i, by omega⟩ =
      (BitVec.adc x y c).2.getLsbD i := by
  simp only [Circuit.eval, rippleCarryAdder, Function.comp_apply, hi, ↓reduceDIte,
    Program.trace]
  rw [Wire.elim_gate, rcaProgram_eval, BitVec.adc_spec, BitVec.getLsbD_add_add_bool hi]
  have e1 : (5 * i + 1) % 5 = 1 := by omega
  have e2 : (5 * i + 1) / 5 = i := by omega
  simp only [rcaSpec, e1, e2]
  simp

/-- **Carry out**: output `n` is the carry `(BitVec.adc x y c).1`. -/
theorem rippleCarryAdder_carry :
    (rippleCarryAdder n).eval arithInterpretation (rcaInput x y c) ⟨n, by omega⟩ =
      (BitVec.adc x y c).1 := by
  have hn : ¬ n < n := Nat.lt_irrefl n
  simp only [Circuit.eval, rippleCarryAdder, Function.comp_apply, hn, ↓reduceDIte,
    Program.trace]
  rw [carryWire_value x y c (Nat.le_refl _) _ (rcaProgram_eval x y c (5 * n) (Nat.le_refl _)),
    BitVec.adc_spec]

/-- The `n`-bit adder has `5 n` gates. -/
theorem rippleCarryAdder_size : (rippleCarryAdder n).size = 5 * n := rfl

end Cslib.Circuits
