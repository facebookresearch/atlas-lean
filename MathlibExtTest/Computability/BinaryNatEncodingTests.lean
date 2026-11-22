/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Tests for the Mathlib binary natural-number encoding wrapper.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding

@[expose] public section

namespace MathlibExtTest.Computability.BinaryNatEncodingTests

open MetaMathlibExt.BinaryNatEncoding
open MetaMathlibExt.BitstringEncoding

/-- Mathlib encodes zero by the empty bitstring. -/
example : Computability.encodeNat 0 = [] := rfl

/-- Mathlib's encoding is little-endian binary. -/
example : Computability.encodeNat 5 = [true, false, true] := rfl

/-- Mathlib's decoder round-trips its natural-number encoding. -/
example : Computability.decodeNat (Computability.encodeNat 37) = 37 :=
  Computability.decode_encodeNat 37

/-- The bitstring instance is Mathlib's binary natural encoding. -/
example : bitEncode 37 = Computability.encodeNat 37 := bitEncode_nat 37

/-- The bitstring instance round-trips a natural number. -/
example : bitDecode (bitEncode 37) = some 37 :=
  bitDecode_bitEncode 37

/-- Mathlib's encoding length is the binary size, including length
zero at zero. -/
example (n : ℕ) : (Computability.encodeNat n).length = n.size :=
  length_encodeNat n

/-- The generic pair encoder delimits Mathlib's first-component
encoding and appends Mathlib's second-component encoding. -/
example :
    bitEncode (5, 2) =
      delimit (Computability.encodeNat 5) ++ Computability.encodeNat 2 := rfl

/-- Pair decoding through the generic bitstring instance round-trips. -/
example : bitDecode (bitEncode (5, 2)) = some (5, 2) :=
  bitDecode_bitEncode (5, 2)

/-- The generic pair encoding has length linear in the two input sizes. -/
example :
    (bitEncode (5, 2)).length =
      2 * (5 : ℕ).size + (2 : ℕ).size + 1 :=
  bitEncode_pair_nat_length (5, 2)

end MathlibExtTest.Computability.BinaryNatEncodingTests
