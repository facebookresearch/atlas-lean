/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.ListCount

open Turing MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.PolynomialEncoding
open ListCount

set_option maxRecDepth 10000

private def drive {J : Type} [DecidableEq J]
    (P : Lab → TM2.Stmt (fun _ : J => Bool) Lab Bool) :
    Nat → TM2.Cfg (fun _ : J => Bool) Lab Bool →
      Option (TM2.Cfg (fun _ : J => Bool) Lab Bool)
  | 0, _ => none
  | n + 1, c =>
    if c.l = some .good ∨ c.l = some .bad then some c
    else (TM2.step P c).bind (drive P n)

private def checkGood (x : List Bool) (n : Nat) (suffix : List Bool) : Bool :=
  match drive prog (4 * x.length + 3) ⟨some .loop, true, st x [] suffix⟩ with
  | none => false
  | some c => c.l == some .good && c.stk .input == [] &&
      c.stk .scratch == [] && c.stk .count == List.replicate n true ++ suffix

private def checkBad (x : List Bool) : Bool :=
  match drive prog (4 * x.length + 3) ⟨some .loop, false, st x [] []⟩ with
  | none => false
  | some c => c.l == some .bad

example : checkGood [] 0 [false, true] = true := by decide
example : checkGood [false, false] 2 [false] = true := by decide
example : checkGood [true, false, false] 1 [false, true] = true := by decide
example : checkGood (bitEncode ([0, 2, 5] : List Nat)) 3 [] = true := by decide
example : checkGood (delimit (List.replicate 12 false)) 1 [] = true := by decide
example : checkBad [true] = true := by decide
example : checkBad [true, false] = true := by decide
example : checkBad [false, true] = true := by decide
example : checkBad [true, true, false, true, false] = true := by decide

private def extension : MetaMathlibExt.TM2Embedding.SEmb
    (fun _ : K => Bool) (fun _ : Option K => Bool) where
  e := some
  inj := fun _ _ h => Option.some.inj h
  ι _ := Equiv.refl Bool

private def checkFrame (x : List Bool) : Bool :=
  let P := fun l => MetaMathlibExt.TM2Embedding.mapS extension id (prog l)
  let S : Option K → List Bool
    | none => [true, false, true]
    | some k => st x [] [] k
  match drive P (4 * x.length + 3) ⟨some .loop, false, S⟩ with
  | none => false
  | some c => c.stk none == [true, false, true] &&
      c.l == some (if (bitDecode (α := List Nat) x).isSome then .good else .bad)

example : checkFrame [true, false, false, false] = true := by decide
example : checkFrame [false, true] = true := by decide

example {x : List Bool} {as : List Nat} (h : bitDecode x = some as) :
    (List.replicate as.length true).length ≤ x.length := by
  simpa using decoded_list_length_le h

example {x : List Bool} {as : List Nat} (h : bitDecode x = some as)
    (suffix : List Bool) (v : Bool) :
    MetaMathlibExt.TM2Program.RunLe prog (4 * x.length + 1)
      ⟨some .loop, v, st x [] suffix⟩
      ⟨some .good, false, st [] [] (List.replicate as.length true ++ suffix)⟩ :=
  run_some h suffix v
