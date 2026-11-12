/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts
import MathlibExt.Computability.BinaryNatEncoding

open MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.PolynomialEncoding

example (p r : List Bool) :
    bitDecode (α := List (Bool × Nat)) (delimit p ++ r) =
      (bitDecode (α := Bool × Nat) p).bind (fun a =>
        (bitDecode (α := List (Bool × Nat)) r).map (a :: ·)) :=
  decode_list_delimit p r

example {x : List Bool} (hx : x ≠ []) (h : undelimit x = none) :
    bitDecode (α := List (Nat × Nat)) x = none :=
  decode_list_none_of_undelimit_none hx h

example : bitDecode (α := List Bool) [] = some [] := by decide
example : bitDecode (α := List Bool) [false] = none := by decide
example : bitDecode (α := List Bool) [true, false, false] =
    some [false] := by decide
example : bitDecode (α := List Nat) [false] = some [0] := by decide
example : bitDecode (α := List Nat) [true, false, false] =
    some [2] := by decide
example : bitDecode (α := List Bool) [true, false, false, true] =
    none := by decide
example : bitDecode (α := List (Nat × Nat)) (delimit [false] ++ [true]) =
    none := by decide
example : undelimitBlocks (delimit [true, false] ++ [true]) = none := by
  decide
