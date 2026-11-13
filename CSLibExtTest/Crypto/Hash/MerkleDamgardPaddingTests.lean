/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Hash.MerkleDamgardPadding

/-!
# Tests: the Merkle–Damgård length field is the reversed big-endian codec

`encodeLength` / `decodeLength` are defined from `Nat.toBitsBE` / `Nat.ofBitsBE`. The value `1` at
width `4` is not a palindrome (`0001` big-endian, `1000` little-endian), so these examples fail if
the orientation of either codec flips.
-/

namespace CSLibExtTest.Crypto.MerkleDamgardPaddingTests

open Cslib.Crypto.MerkleDamgardPadding

example : Nat.toBitsBE 4 1 = [false, false, false, true] := by decide

example : encodeLength 4 1 = [true, false, false, false] := by decide

example : encodeLength 4 1 = (Nat.toBitsBE 4 1).reverse := rfl

example : decodeLength [true, false, false, false] = 1 := by decide

example : decodeLength [false, false, false, true] = 8 := by decide

example : decodeLength [true, false, true, true] = Nat.ofBitsBE [true, true, false, true] := rfl

example : decodeLength (encodeLength 4 19) = 3 :=
  (decodeLength_encodeLength 4 19).trans (by decide)

example (a : ℕ) (ha : a < 2 ^ 4) (h : encodeLength 4 a = encodeLength 4 9) : a = 9 :=
  encodeLength_injOn ha (by decide) h

end CSLibExtTest.Crypto.MerkleDamgardPaddingTests
