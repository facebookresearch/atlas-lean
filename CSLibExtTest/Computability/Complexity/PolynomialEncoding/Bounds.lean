/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds

open MetaMathlibExt BitstringEncoding
open Cslib.Complexity.PolynomialEncoding

-- The exact canonical Nat instance has total, nontrimming decoding.
example : bitDecode (α := Nat) [false] = some 2 := by decide
example : bitDecode (α := Nat) [true, false] = some 5 := by decide
example : bitDecode (α := List Nat) [true, false, false] =
    some [2] := by decide
example : bitDecode (α := List Nat) [] = some [] := by decide
example : bitDecode (α := List Nat) [true] = none := by decide
example : bitDecode (α := List Nat) [true, false] = none := by decide
example : bitDecode (α := List Nat) [false, false] =
    some [0, 0] := by decide

-- Real consumer types, including right-associated triples.
example {x : List Bool} {as : List (Nat × Nat)} {cap val : Nat}
    (h : bitDecode x = some (as, cap, val)) : as.length ≤ x.length :=
  decoded_fst_list_length_le h
example {x : List Bool} {n b : Nat} {w : List (List Nat)}
    (h : bitDecode x = some (n, w, b)) : w.length ≤ x.length :=
  decoded_middle_list_length_le h
example {x : List Bool} {n : Nat} {gates : List (Nat × Nat × Nat)}
    (h : bitDecode x = some (n, gates)) : gates.length ≤ x.length :=
  decoded_snd_list_length_le h
example : (bitEncode ([] : List Nat)).length ≤ 0 * (2 * 0 + 1) :=
  bounded_nat_list_encode_length_le [] 0 (by decide) (by simp)
example : (bitEncode [0, 1, 1]).length ≤ 3 * (2 * 3 + 1) :=
  bounded_nat_list_encode_length_le [0, 1, 1] 3 (by decide) (by decide)
example : (bitEncode [0, 0, 0]).length = 3 := by decide
