/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit

open Turing MetaMathlibExt BitstringEncoding
open Cslib.Complexity.PolynomialEncoding.PairSplit

private def execute : Nat → TM2.Cfg (fun _ : K => Bool) Lab Bool →
    Option (TM2.Cfg (fun _ : K => Bool) Lab Bool)
  | 0, _ => none
  | n + 1, c => match c.l with
    | some .good | some .bad => some c
    | _ => (TM2.step prog c).bind (execute n)

private def checkGood (x p r out : List Bool) : Bool :=
  match execute (x.length + 2) ⟨some .read, true, st x out []⟩ with
  | none => false
  | some c => decide (c.l = some .good ∧ c.stk .input = r ∧
      c.stk .left = p ++ out ∧ c.stk .scratch = [])

private def checkBad (x : List Bool) : Bool :=
  match execute (x.length + 2) ⟨some .read, false, st x [] []⟩ with
  | none => false
  | some c => decide (c.l = some .bad)

example : checkGood [false] [] [] [] = true := by decide
-- The second field remains raw; projection does not claim it is valid.
example : checkGood [false, true] [] [true] [] = true := by decide
example : checkGood [true, false, false, true]
    [false] [true] [false, true] = true := by decide
example : checkGood (bitEncode ((2, 5) : Nat × Nat))
    (bitEncode (2 : Nat)) (bitEncode (5 : Nat)) [] = true := by decide
example : checkBad [] = true := by decide
example : checkBad [true] = true := by decide
example : checkBad [true, false] = true := by decide

example {x : List Bool} {items : List (Nat × Nat)} {c v : Nat}
    (h : bitDecode x = some (items, c, v)) :
    ∃ p r state, MetaMathlibExt.TM2Program.RunLe prog (x.length + 1)
      ⟨some .read, false, st x [] []⟩ ⟨some .good, state, st r p []⟩ ∧
      bitDecode p = some items ∧ bitDecode r = some (c, v) :=
  run_decoded h false
