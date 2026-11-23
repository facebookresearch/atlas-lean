/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatPair

open Turing MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.PolynomialEncoding
open ListNatPair

set_option maxRecDepth 10000

private def drive {J : Type} [DecidableEq J]
    (P : Lab → TM2.Stmt (fun _ : J => Bool) Lab Bool) :
    Nat → TM2.Cfg (fun _ : J => Bool) Lab Bool →
      Option (TM2.Cfg (fun _ : J => Bool) Lab Bool)
  | 0, _ => none
  | n + 1, c =>
    if c.l = some .good ∨ c.l = some .bad then some c
    else (TM2.step P c).bind (drive P n)

private def checkGood (x : List Bool) (as : List (Nat × Nat))
    (ow ov : List Bool) : Bool :=
  match drive prog (16 * x.length + 4) ⟨some .loop, true,
      st x [] [] ow ov (NatPair.st [] [] [] [] [] [])⟩ with
  | none => false
  | some c => decide (c.l = some .good ∧ c.stk .input = [] ∧
      c.stk (.acc false) = [] ∧ c.stk (.acc true) = [] ∧
      c.stk (.output false) = bitEncode (as.map Prod.fst) ++ ow ∧
      c.stk (.output true) = bitEncode (as.map Prod.snd) ++ ov ∧
      ∀ k, c.stk (.pair k) = [])

private def checkBad (x : List Bool) : Bool :=
  match drive prog (12 * x.length + 3) ⟨some .loop, false,
      st x [] [] [] [] (NatPair.st [] [] [] [] [] [])⟩ with
  | none => false
  | some c => c.l == some .bad

example : checkGood [] [] [true] [false] = true := by decide
example : checkGood (delimit [false, false]) [(0, 2)] [] [] = true := by decide
example : checkGood (bitEncode ([(2, 5), (0, 3)] : List (Nat × Nat)))
    [(2, 5), (0, 3)] [true, false] [false, true] = true := by decide
example : checkGood (bitEncode ([(0, 2), (2, 0), (5, 2)] : List (Nat × Nat)))
    [(0, 2), (2, 0), (5, 2)] [] [] = true := by decide
example : checkBad [false] = true := by decide
example : checkBad [true] = true := by decide
example : checkBad (delimit [true]) = true := by decide
example : checkBad (delimit [false] ++ [true]) = true := by decide
example : checkBad (delimit [false] ++ [false]) = true := by decide

private def extension : MetaMathlibExt.TM2Embedding.SEmb
    (fun _ : K => Bool) (fun _ : Option K => Bool) where
  e := some
  inj := fun _ _ h => Option.some.inj h
  ι _ := Equiv.refl Bool

private def checkFrame (x : List Bool) : Bool :=
  let P := fun l => MetaMathlibExt.TM2Embedding.mapS extension id (prog l)
  let S : Option K → List Bool
    | none => [true, false, true]
    | some k => st x [] [] [] [] (NatPair.st [] [] [] [] [] []) k
  match drive P (16 * x.length + 4) ⟨some .loop, false, S⟩ with
  | none => false
  | some c => c.stk none == [true, false, true] &&
      c.l == some (if (bitDecode (α := List (Nat × Nat)) x).isSome
        then .good else .bad)

example : checkFrame (delimit [false, false]) = true := by decide
example : checkFrame (delimit [false] ++ [true]) = true := by decide
example : checkFrame [false] = true := by decide
