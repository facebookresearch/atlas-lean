/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.Arithmetic.CarryLookahead

/-!
# Two's complement: subtraction and signed overflow with the adders

The two's complement tie-in of the adders to `BitVec` (Harris and Harris, *Digital Design and
Computer Architecture*, second edition (2012), Sections 1.4.6 (signed numbers) and 5.2.2
(subtraction)):

* `adc_not_true`: `x - y = x + ~~~y + 1`, and the carry out of that addition is set exactly when
  there is no unsigned borrow (`!x.usubOverflow y`); hence the ripple-carry and carry-lookahead
  adders subtract when fed `~~~y` and carry in `1` (`rippleCarryAdder_sub`,
  `rippleCarryAdder_noBorrow`, `carryLookaheadAdder_sub`, `carryLookaheadAdder_noBorrow`).
* `saddOverflow_eq_carry_xor`: the signed overflow of `x + y` (`BitVec.saddOverflow`) is the XOR
  of the carries into and out of the sign bit.
* `overflowAdder`: the ripple-carry adder with one more XOR gate computing that flag;
  `overflowAdder_sum` (sum bits), `overflowAdder_eval_of_lt` (sum and carry as the adder's),
  `overflowAdder_overflow` (the flag equals `x.saddOverflow y`), `overflowAdder_size`
  (`5 n + 1` gates).

## Cost model

Circuit size (CSLib's `Circuit.size`); feeding `~~~y` is done by the caller, outside the circuit
(the gate set has no NOT gate; a NOT costs one XOR with a constant-`1` input).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Circuits

open RippleCarry CarryLookahead

variable {n : ℕ} (x y : BitVec n)

/-! ## Subtraction -/

/-- **Subtraction by addition**: adding `~~~y` with carry in `1` computes `x - y`, and the carry
out is set exactly when there is no unsigned borrow (`y ≤ x`). -/
theorem adc_not_true : BitVec.adc x (~~~y) true = (!x.usubOverflow y, x - y) := by
  rw [BitVec.adc_spec, BitVec.carry_width, BitVec.toNat_not]
  have hy := y.isLt
  congr 1
  · simp only [BitVec.usubOverflow, Bool.toNat_true]
    rw [Bool.eq_iff_iff]
    simp only [ge_iff_le, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    omega
  · rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
    congr 2
    cases n with
    | zero => exact Subsingleton.elim _ _
    | succ n =>
        apply BitVec.eq_of_toNat_eq
        have : 1 < 2 ^ (n + 1) := Nat.one_lt_two_pow (Nat.succ_ne_zero n)
        simp [Nat.mod_eq_of_lt this]

/-- The ripple-carry adder subtracts: with `~~~y` and carry in `1`, sum bit `i` is bit `i` of
`x - y`. -/
theorem rippleCarryAdder_sub (i : ℕ) (hi : i < n) :
    (rippleCarryAdder n).eval arithInterpretation (rcaInput x (~~~y) true) ⟨i, by omega⟩ =
      (x - y).getLsbD i := by
  rw [rippleCarryAdder_sum _ _ _ i hi, adc_not_true]

/-- With `~~~y` and carry in `1`, the ripple-carry adder's carry out is "no unsigned borrow". -/
theorem rippleCarryAdder_noBorrow :
    (rippleCarryAdder n).eval arithInterpretation (rcaInput x (~~~y) true) ⟨n, by omega⟩ =
      !x.usubOverflow y := by
  rw [rippleCarryAdder_carry, adc_not_true]

/-- The carry-lookahead adder subtracts the same way (`n ≤ 2 ^ K`). -/
theorem carryLookaheadAdder_sub {K : ℕ} (hK : n ≤ 2 ^ K) (i : ℕ) (hi : i < n) :
    (carryLookaheadAdder n K).eval arithInterpretation (rcaInput x (~~~y) true)
        ⟨i, by omega⟩ = (x - y).getLsbD i := by
  rw [carryLookaheadAdder_sum _ _ _ hK i hi, adc_not_true]

theorem carryLookaheadAdder_noBorrow {K : ℕ} (hK : n ≤ 2 ^ K) :
    (carryLookaheadAdder n K).eval arithInterpretation (rcaInput x (~~~y) true)
        ⟨n, by omega⟩ = !x.usubOverflow y := by
  rw [carryLookaheadAdder_carry _ _ _ hK, adc_not_true]

/-! ## Signed overflow -/

/-- **Signed overflow is the XOR of the last two carries**: for `n ≥ 1`, the two's complement sum
`x + y` overflows exactly when the carry into the sign bit differs from the carry out of it. -/
theorem saddOverflow_eq_carry_xor (hn : 0 < n) :
    x.saddOverflow y = (BitVec.carry (n - 1) x y false ^^ BitVec.carry n x y false) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [BitVec.saddOverflow_eq, BitVec.msb_add, Nat.add_sub_cancel, BitVec.carry_succ]
  simp only [BitVec.msb_eq_getLsbD_last, Nat.add_sub_cancel]
  cases x.getLsbD m <;> cases y.getLsbD m <;> cases BitVec.carry m x y false <;> rfl

/-- The ripple-carry adder with a signed-overflow flag: one more XOR gate on the last two
carries. Outputs: the `n` sum bits, the carry out, and the overflow flag. -/
def overflowAdder (n : ℕ) : Circuit arithSignature (2 * n + 1) (n + 2) where
  size := 5 * n + 1
  program := (rcaProgram n (5 * n) (Nat.le_refl _)).gate
    (binLine .xor (carryWire n (5 * n) (n - 1) (by omega)) (carryWire n (5 * n) n (Nat.le_refl _)))
  outputs o :=
    if h : o.val < n + 1 then Wire.castSucc ((rippleCarryAdder n).outputs ⟨o.val, h⟩)
    else Wire.gate (Fin.last (5 * n))

/-- The first `n + 1` outputs of `overflowAdder` are those of the ripple-carry adder. -/
theorem overflowAdder_eval_of_lt (c : Bool) (o : ℕ) (ho : o < n + 1) :
    (overflowAdder n).eval arithInterpretation (rcaInput x y c) ⟨o, by omega⟩ =
      (rippleCarryAdder n).eval arithInterpretation (rcaInput x y c) ⟨o, ho⟩ := by
  simp only [Circuit.eval, overflowAdder, Function.comp_apply, ho, ↓reduceDIte]
  exact Program.trace_gate_castSucc _ _ arithInterpretation _ _

/-- **The overflow flag**: for `n ≥ 1` and carry in `0`, the last output of `overflowAdder` is
`BitVec.saddOverflow x y`, the signed (two's complement) overflow of `x + y`. -/
theorem overflowAdder_overflow (hn : 0 < n) :
    (overflowAdder n).eval arithInterpretation (rcaInput x y false) ⟨n + 1, by omega⟩ =
      x.saddOverflow y := by
  have hno : ¬ (n + 1 < n + 1) := Nat.lt_irrefl _
  simp only [Circuit.eval, overflowAdder, Function.comp_apply, hno, ↓reduceDIte, Program.trace,
    Wire.elim_gate, Program.eval_gate_last, binLine_eval]
  have hg := rcaProgram_eval x y false (5 * n) (Nat.le_refl _)
  rw [carryWire_value x y false _ _ hg, carryWire_value x y false _ _ hg,
    saddOverflow_eq_carry_xor x y hn]
  rfl

/-- The sum bits of `overflowAdder` are those of `x + y` (carry in `0`). -/
theorem overflowAdder_sum (i : ℕ) (hi : i < n) :
    (overflowAdder n).eval arithInterpretation (rcaInput x y false) ⟨i, by omega⟩ =
      (x + y).getLsbD i := by
  rw [overflowAdder_eval_of_lt x y false i (by omega), rippleCarryAdder_sum _ _ _ i hi,
    BitVec.adc_spec]
  cases n with
  | zero => omega
  | succ n => simp

/-- The size: one gate more than the ripple-carry adder. -/
theorem overflowAdder_size : (overflowAdder n).size = 5 * n + 1 := rfl

end Cslib.Circuits
