/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.NatPair

open Turing MetaMathlibExt BitstringEncoding
open Cslib.Complexity.PolynomialEncoding.NatPair

set_option maxRecDepth 10000

private def execute : Nat → TM2.Cfg (fun _ : K => Bool) Lab Bool →
    Option (TM2.Cfg (fun _ : K => Bool) Lab Bool)
  | 0, _ => none
  | n + 1, c => match c.l with
    | some .good | some .bad => some c
    | _ => (TM2.step prog c).bind (execute n)

private def checkGood (x : List Bool) (m n : Nat)
    (left right : List Bool) : Bool :=
  match execute (2 * x.length + 7)
      ⟨some (.pair .read), true, st x [] [] [] left right⟩ with
  | none => false
  | some c => decide (c.l = some .good ∧
      c.stk .left = Computability.encodeNat m ++ left ∧
      c.stk .right = Computability.encodeNat n ++ right ∧
      c.stk (.pair .input) = [] ∧ c.stk (.pair .left) = [] ∧
      c.stk (.pair .scratch) = [] ∧ c.stk .buffer = [])

private def checkBad (x : List Bool) : Bool :=
  match execute (2 * x.length + 7)
      ⟨some (.pair .read), false, st x [] [] [] [] []⟩ with
  | none => false
  | some c => decide (c.l = some .bad)

example : checkGood [false] 0 0 [] [] = true := by decide
example : checkGood [false, false] 0 2 [] [] = true := by decide
example : checkGood [true, false, false, false] 2 2 [] [] = true := by decide
example : checkGood [true, true, true, false, false, false]
    5 2 [true] [false] = true := by decide
example : checkGood (bitEncode ((5, 8) : Nat × Nat)) 5 8 [] [] = true := by
  decide
example : checkBad [] = true := by decide
example : checkBad [true] = true := by decide
example : checkBad [true, false] = true := by decide

example {x : List Bool} {m n : Nat} (h : bitDecode x = some (m, n)) :
    (Computability.encodeNat m).length + (Computability.encodeNat n).length ≤
      x.length + 1 := decoded_payload_length_le h
