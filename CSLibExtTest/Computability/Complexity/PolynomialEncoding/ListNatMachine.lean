/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatMachine

open Turing MetaMathlibExt BitstringEncoding
open Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.PolynomialEncoding.ListNatMachine
open Cslib.Complexity.FramedCNF

set_option maxRecDepth 10000

private def execute : Nat → TM2.Cfg (fun _ : K => Bool) Lab Bool →
    Option (TM2.Cfg (fun _ : K => Bool) Lab Bool)
  | 0, _ => none
  | n + 1, c => match c.l with
    | some .good | some .bad => some c
    | _ => (TM2.step prog c).bind (execute n)

private def checkGood (x expected out : List Bool) : Bool :=
  match execute (11 * x.length + 3)
      ⟨some .loop, true, st x [] out (NormalizeMachine.st [] [] [])⟩ with
  | none => false
  | some c => decide (c.l = some .good ∧ c.stk .output = expected ++ out ∧
      c.stk .input = [] ∧ c.stk .acc = [] ∧ c.stk (.nat .input) = [] ∧
      c.stk (.nat .buffer) = [] ∧ c.stk (.nat .output) = [])

private def checkBad (x : List Bool) : Bool :=
  match execute (11 * x.length + 3)
      ⟨some .loop, false, st x [] [] (NormalizeMachine.st [] [] [])⟩ with
  | none => false
  | some c => decide (c.l = some .bad)

-- Successful boundaries and noncanonical inputs use the actual program.
example : checkGood [] [] [true, false] = true := by decide
example : checkGood [false, false] (bitEncode [0, 0]) [] = true := by decide
example : checkGood [true, false, false] (bitEncode [2]) [] = true := by decide
example : checkGood [true, true, true, false, false]
    (bitEncode [5]) [false, true] = true := by decide
example : checkGood (bitEncode [0, 1, 2, 5])
    (bitEncode [0, 1, 2, 5]) [] = true := by decide

-- Truncated blocks reject, including after a complete zero payload.
example : checkBad [true] = true := by decide
example : checkBad [true, false] = true := by decide
example : checkBad [false, true] = true := by decide
example : checkBad [true, false, false, true, true] = true := by decide

-- Exact semantic and size contracts remain available to callers.
example {x : List Bool} {as : List Nat} (h : bitDecode x = some as) :
    (bitEncode as).length ≤ 3 * x.length :=
  decoded_list_nat_encode_length_le h
example {x : List Bool} {as : List Nat} (h : bitDecode x = some as) :
    ∃ v, MetaMathlibExt.TM2Program.RunLe prog (11 * x.length + 2)
      ⟨some .loop, false, st x [] [] (NormalizeMachine.st [] [] [])⟩
      ⟨some .good, v, st [] [] (bitEncode as)
        (NormalizeMachine.st [] [] [])⟩ := by
  simpa using run_some h [] false
