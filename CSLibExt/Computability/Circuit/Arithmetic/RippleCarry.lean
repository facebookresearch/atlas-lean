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

/-- **Arithmetic gate symbols.** The gate symbols of arithmetic circuits are exactly three:
XOR, AND and OR. -/
inductive ArithGate where
  | xor
  | and
  | or
  deriving Repr, DecidableEq

/-- **Arithmetic basis.** The circuit signature whose operation symbols are the three arithmetic
gate symbols XOR, AND and OR, each of arity $2$. -/
def arithSignature : Signature where
  Op := ArithGate
  Arity _ := 2

/-- **Boolean interpretation of the arithmetic gates.** The interpretation of the arithmetic
basis in the Booleans: on a first argument $a$ and a second argument $b$, the XOR gate computes
$a \oplus b$, the AND gate computes $a \wedge b$, and the OR gate computes $a \vee b$. -/
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

/-- **Binary gate line.** For an arithmetic gate symbol $\mathrm{op}$ and wires $u$ and $v$ of a
circuit with $m$ inputs (each wire is an input or one of the $g$ preceding gates), the gate that
applies $\mathrm{op}$ to $u$ as its first argument and $v$ as its second. -/
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

/-- **Carry wire.** For natural numbers $n$, $g$ and $i$ with $5i \le g$, the wire carrying the
carry into bit $i$ of the $n$-bit adder, in a circuit with $2n + 1$ inputs and $g$ gates: for
$i = 0$ it is the carry-in input (input $2n$), and for $i \ne 0$ it is gate $5i - 1$, the
carry-out gate of bit $i - 1$. -/
def carryWire (n g i : ℕ) (hi : 5 * i ≤ g) : Wire (2 * n + 1) g :=
  if h : i = 0 then Wire.input ⟨2 * n, by omega⟩ else Wire.gate ⟨5 * i - 1, by omega⟩

/-- **Gates of the ripple-carry adder.** For natural numbers $n$ and $g$ with $g < 5n$, gate $g$ of
the $n$-bit ripple-carry adder is the following binary gate of the arithmetic basis, whose
arguments are among the $2n + 1$ inputs and the $g$ gates before it. Write $g = 5i + r$ with
$0 \le r < 5$, let $a$ be input $i$ and $b$ input $n + i$, and let $c$ be the carry into bit $i$:
input $2n$ if $i = 0$ and gate $5i - 1$ otherwise. Gate $g$ is the XOR gate with first argument
$a$ and second argument $b$ if $r = 0$, the XOR gate with first argument gate $g - 1$ and second
argument $c$ if $r = 1$, the AND gate with first argument $a$ and second argument $b$ if $r = 2$,
the AND gate with first argument gate $g - 3$ and second argument $c$ if $r = 3$, and the OR gate
with first argument gate $g - 2$ and second argument gate $g - 1$ if $r = 4$. -/
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

/-- **Gate program of the ripple-carry adder.** For $g \le 5n$, the straight-line program over the
arithmetic basis with $2n + 1$ inputs whose gates are, in order, gates $0, 1, \dots, g - 1$ of
the $n$-bit ripple-carry adder; for $g = 0$ it is the empty program. -/
def rcaProgram (n : ℕ) : (g : ℕ) → g ≤ 5 * n → Program arithSignature (2 * n + 1) g
  | 0, _ => .empty
  | g + 1, h => (rcaProgram n g (by omega)).gate (line n g (by omega))

/-- **Ripple-carry adder.** The $n$-bit ripple-carry adder is the circuit with $2n + 1$ inputs,
$5n$ binary gates, each an XOR, AND or OR gate, and $n + 1$ outputs, built as follows. Write $a_i$
for input $i$, $b_i$ for input $n + i$ and $c_0$ for input $2n$, where $i < n$. For each $i < n$,
gates $g_{5i}, \dots, g_{5i+4}$ form a full adder for position $i$: $g_{5i} = a_i \oplus b_i$,
$g_{5i+1} = g_{5i} \oplus c_i$, $g_{5i+2} = a_i \wedge b_i$, $g_{5i+3} = g_{5i} \wedge c_i$ and
$g_{5i+4} = g_{5i+2} \vee g_{5i+3}$, where the carry $c_i$ is input $2n$ when $i = 0$ and gate
$g_{5i-1}$ otherwise. For $i < n$, output $i$ is gate $g_{5i+1}$, and output $n$ is the carry out
$c_n$: input $2n$ when $n = 0$, otherwise gate $g_{5n-1}$. -/
def rippleCarryAdder (n : ℕ) : Circuit arithSignature (2 * n + 1) (n + 1) where
  size := 5 * n
  program := rcaProgram n (5 * n) (Nat.le_refl _)
  outputs o := if h : o.val < n then Wire.gate ⟨5 * o.val + 1, by omega⟩
    else carryWire n (5 * n) n (Nat.le_refl _)

/-- **Input of the ripple-carry adder.** For $n$-bit vectors $x$ and $y$ and a bit $c$, the
assignment to the $2n + 1$ inputs of the $n$-bit adder: for $j < n$, input $j$ is bit $j$ of
$x$; for $n \le j < 2n$, input $j$ is bit $j - n$ of $y$; and input $2n$ is $c$. Bit $0$ is the
least significant bit. -/
def rcaInput {n : ℕ} (x y : BitVec n) (c : Bool) : Fin (2 * n + 1) → Bool := fun j =>
  if j.val < n then x.getLsbD j.val else if j.val < 2 * n then y.getLsbD (j.val - n) else c

/-- **Gate-value specification of the ripple-carry adder.** Let $x, y$ be $n$-bit vectors, $c$ a
bit and $j$ a natural number, and write $j = 5i + r$ with $0 \le r < 5$. Let $x_i$ and $y_i$ be
bit $i$ of $x$ and $y$ (bit $0$ is the least significant, and bits at positions $i \ge n$ are $0$),
and let $c_i$ be the carry into position $i$ when $x$, $y$ and $c$ are added: reading $x$ and $y$
as natural numbers, $c_i = 1$ exactly when $(x \bmod 2^i) + (y \bmod 2^i) + c \ge 2^i$. The
specification assigns to $j$ the bit $x_i \oplus y_i$ if $r = 0$, $(x_i \oplus y_i) \oplus c_i$
if $r = 1$, $x_i \wedge y_i$ if $r = 2$, $(x_i \oplus y_i) \wedge c_i$ if $r = 3$, and $c_{i+1}$
if $r = 4$. -/
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

/-- **Value of the carry wire.** Let $x$ and $y$ be $n$-bit vectors, $c$ a bit, and $i$ and $g$
natural numbers with $5i \le g$. Suppose the first $g$ gates are given values $v_0, \dots, v_{g-1}$
with each $v_j$ equal to the specified value of gate $j$ of the adder on $x$, $y$, $c$. Then, on
the adder input for $x$, $y$, $c$ and with these gate values, the carry wire into bit $i$ carries
the carry into bit $i$ of $x + y + c$: it is true exactly when
$(x \bmod 2^i) + (y \bmod 2^i) + c \ge 2^i$, reading $x$, $y$ and $c$ as natural numbers. -/
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

/-- **Gate values of the ripple-carry adder.** Let $x$ and $y$ be $n$-bit vectors and $c$ a bit.
For every $g \le 5n$ and every $j < g$, evaluating the first $g$ gates of the $n$-bit adder with
the Boolean interpretation of the arithmetic gates on the adder input for $x$, $y$, $c$ gives
gate $j$ its specified value on $x$, $y$, $c$. -/
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

/-- **Sum bits of the ripple-carry adder.** Let $x, y$ be $n$-bit vectors, $c$ a bit and $i < n$,
and evaluate the $n$-bit ripple-carry adder, with its gates read as Boolean XOR, AND and OR, on the
input whose entry $j$ is bit $j$ of $x$ and entry $n + j$ is bit $j$ of $y$ for $j < n$ (bit $0$
being the least significant), and whose entry $2n$ is $c$. Its output number $i$ (outputs being
numbered from $0$) is bit $i$ of the $n$-bit sum $(x + y + c) \bmod 2^n$, reading $x$ and $y$ as
natural numbers below $2^n$. -/
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

/-- **Carry out of the ripple-carry adder.** Let $x, y$ be $n$-bit vectors and $c$ a bit, and
evaluate the $n$-bit ripple-carry adder, with its gates read as Boolean XOR, AND and OR, on the
input whose entry $j$ is bit $j$ of $x$ and entry $n + j$ is bit $j$ of $y$ for $j < n$ (bit $0$
being the least significant), and whose entry $2n$ is $c$. Its output number $n$ (the last,
outputs being numbered from $0$) is the carry out of $x + y + c$: reading $x$ and $y$ as natural
numbers below $2^n$, it is $1$ exactly when $x + y + c \ge 2^n$. -/
theorem rippleCarryAdder_carry :
    (rippleCarryAdder n).eval arithInterpretation (rcaInput x y c) ⟨n, by omega⟩ =
      (BitVec.adc x y c).1 := by
  have hn : ¬ n < n := Nat.lt_irrefl n
  simp only [Circuit.eval, rippleCarryAdder, Function.comp_apply, hn, ↓reduceDIte,
    Program.trace]
  rw [carryWire_value x y c (Nat.le_refl _) _ (rcaProgram_eval x y c (5 * n) (Nat.le_refl _)),
    BitVec.adc_spec]

/-- **Size of the ripple-carry adder.** The $n$-bit ripple-carry adder has exactly $5n$ gates. -/
theorem rippleCarryAdder_size : (rippleCarryAdder n).size = 5 * n := rfl

end Cslib.Circuits
