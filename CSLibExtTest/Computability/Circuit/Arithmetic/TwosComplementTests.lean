/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.Arithmetic.TwosComplement
public meta import CSLibExt.Computability.Circuit.Arithmetic.TwosComplement

/-!
# Two's complement tests

Executed fixtures (CSLib's `Circuit.eval`): on all inputs of width 1 and 2, the ripple-carry adder
fed `~~~y` and carry in `1` outputs the bits of `x - y` and the no-borrow flag, and the overflow
adder outputs the bits of `x + y` and `BitVec.saddOverflow x y`; the 1-bit carry-lookahead adder
subtracts on all inputs. Each run throws on a mismatch. Closed checks instantiate the theorems.
-/

namespace Cslib.Circuits

open CarryLookahead

private meta def checkWidth (n : ℕ) : IO Unit := do
  for a in List.range (2 ^ n) do
    for b in List.range (2 ^ n) do
      let x := BitVec.ofNat n a
      let y := BitVec.ofNat n b
      let sub := (rippleCarryAdder n).eval arithInterpretation (rcaInput x (~~~y) true)
      let ovf := (overflowAdder n).eval arithInterpretation (rcaInput x y false)
      for i in List.range n do
        if h : i < n then
          unless sub ⟨i, by omega⟩ == (x - y).getLsbD i do
            throw (IO.userError s!"width {n}: {a} - {b}, bit {i}")
          unless ovf ⟨i, by omega⟩ == (x + y).getLsbD i do
            throw (IO.userError s!"width {n}: {a} + {b}, bit {i}")
      unless sub ⟨n, by omega⟩ == !x.usubOverflow y do
        throw (IO.userError s!"width {n}: borrow of {a} - {b}")
      unless ovf ⟨n + 1, by omega⟩ == x.saddOverflow y do
        throw (IO.userError s!"width {n}: overflow of {a} + {b}")
  IO.println s!"width {n}: subtraction, no-borrow and signed overflow agree with BitVec on all \
    {4 ^ n} inputs"

#eval do
  checkWidth 1
  checkWidth 2
  for a in [0, 1] do
    for b in [0, 1] do
      let x := BitVec.ofNat 1 a
      let y := BitVec.ofNat 1 b
      let out := (carryLookaheadAdder 1 1).eval arithInterpretation (rcaInput x (~~~y) true)
      unless out 0 == (x - y).getLsbD 0 && out 1 == !x.usubOverflow y do
        throw (IO.userError s!"carry-lookahead: {a} - {b}")
  IO.println "1-bit carry-lookahead adder subtracts on all inputs"

-- signed overflow at width 2 (range -2..1): which sums overflow
#eval IO.println s!"width-2 signed overflows: {(List.range 4).flatMap fun a =>
  (List.range 4).filterMap fun b => if (BitVec.ofNat 2 a).saddOverflow (BitVec.ofNat 2 b) then
    some ((BitVec.ofNat 2 a).toInt, (BitVec.ofNat 2 b).toInt) else none}"

/-! Closed checks -/

example (x y : BitVec 64) (i : ℕ) (hi : i < 64) :
    (rippleCarryAdder 64).eval arithInterpretation (rcaInput x (~~~y) true) ⟨i, by omega⟩ =
      (x - y).getLsbD i :=
  rippleCarryAdder_sub x y i hi

example (x y : BitVec 64) :
    (overflowAdder 64).eval arithInterpretation (rcaInput x y false) ⟨65, by omega⟩ =
      x.saddOverflow y :=
  overflowAdder_overflow x y (by decide)

#print axioms adc_not_true
#print axioms saddOverflow_eq_carry_xor
#print axioms overflowAdder_overflow
#print axioms carryLookaheadAdder_sub

end Cslib.Circuits
