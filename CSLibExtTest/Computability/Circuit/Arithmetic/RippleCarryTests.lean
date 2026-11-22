/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.Arithmetic.RippleCarry
public meta import CSLibExt.Computability.Circuit.Arithmetic.RippleCarry

/-!
# Ripple-carry adder tests

Executed fixtures: the circuit's outputs (CSLib's `Circuit.eval`) are compared with
`BitVec.adc` on every input of the 1- and 2-bit adders (`8` and `32` cases) and on 8
pseudo-random inputs of the 3-bit adder; the gate count is checked to be `5 n`, and the depth
measured with CSLib's `Circuit.depth` is printed for `n ≤ 3` (no depth theorem is claimed). Each
run throws on a mismatch. CSLib's evaluator recomputes a gate every time it is read, so its cost
grows exponentially with the gate count and larger adders are covered by the proofs
(`rcaProgram_eval`) rather than by execution. Closed checks instantiate the theorems.
-/

namespace Cslib.Circuits

/-- Run the adder and compare with `BitVec.adc`. -/
private meta def agrees (n : ℕ) (a b : ℕ) (c : Bool) : Bool :=
  let x := BitVec.ofNat n a
  let y := BitVec.ofNat n b
  let out := (rippleCarryAdder n).eval arithInterpretation (rcaInput x y c)
  let r := BitVec.adc x y c
  (List.range n).all (fun i => if h : i < n then out ⟨i, by omega⟩ == r.2.getLsbD i else true) &&
    out ⟨n, by omega⟩ == r.1

#eval do
  for n in [1, 2] do
    let mut count := 0
    for a in List.range (2 ^ n) do
      for b in List.range (2 ^ n) do
        for c in [false, true] do
          unless agrees n a b c do
            throw (IO.userError s!"{n}-bit adder wrong at {a} + {b} + {c}")
          count := count + 1
    IO.println s!"{n}-bit adder agrees with BitVec.adc on all {count} inputs"

#eval do
  for (a, b, c) in [(0, 0, false), (7, 7, true), (5, 3, false), (6, 1, true), (4, 4, false),
      (1, 6, false), (3, 5, true), (7, 0, true)] do
    unless agrees 3 a b c do throw (IO.userError s!"3-bit adder wrong at {a} + {b} + {c}")
  IO.println "3-bit adder agrees with BitVec.adc on 8 inputs"

#eval do
  for n in [1, 2, 3, 8, 16] do
    unless (rippleCarryAdder n).size == 5 * n do throw (IO.userError s!"size of {n}-bit adder")
  for n in [1, 2, 3] do
    IO.println s!"{n}-bit adder: {(rippleCarryAdder n).size} gates, \
      depth {(rippleCarryAdder n).depth}"

/-! Closed checks -/

example (f : Fin 2 → Bool) :
    arithInterpretation .xor f = (f 0 ^^ f 1) ∧ arithInterpretation .and f = (f 0 && f 1) ∧
      arithInterpretation .or f = (f 0 || f 1) := by simp

example (x y : BitVec 8) (c : Bool) :
    (rippleCarryAdder 8).eval arithInterpretation (rcaInput x y c) ⟨8, by omega⟩ =
      (BitVec.adc x y c).1 :=
  rippleCarryAdder_carry x y c

#print axioms arithInterpretation_xor
#print axioms rippleCarryAdder_sum
#print axioms rippleCarryAdder_carry
#print axioms rippleCarryAdder_size
#print axioms rcaProgram_eval

end Cslib.Circuits
