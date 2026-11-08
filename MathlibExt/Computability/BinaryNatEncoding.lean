/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.Encoding
public import Mathlib.Data.Nat.Size
public import MathlibExt.Computability.Complexity

/-!
# Mathlib's binary encoding of natural numbers

This module installs Mathlib's existing `Computability.encodingNatBool`
as the `BitstringEncoding` of natural numbers and records the length
facts needed by complexity statements. It deliberately does not define
a second natural-number encoder, parser, or decoder. Consequently the
generic product instance frames the first component once, directly
around Mathlib's `Computability.encodeNat` payload.
-/

@[expose] public section

namespace MetaMathlibExt.BinaryNatEncoding

open BitstringEncoding

/-- The canonical bitstring encoding of a natural number is Mathlib's
binary `Computability.encodingNatBool`. -/
instance : BitstringEncoding ℕ where
  toEncoding := Computability.encodingNatBool

@[simp]
theorem bitEncode_nat (n : ℕ) :
    bitEncode n = Computability.encodeNat n := rfl

private theorem length_encodePosNum (p : PosNum) :
    (Computability.encodePosNum p).length = p.natSize := by
  induction p with
  | one => rfl
  | bit0 p ih => simp [Computability.encodePosNum, PosNum.natSize, ih]
  | bit1 p ih => simp [Computability.encodePosNum, PosNum.natSize, ih]

private theorem length_encodeNum (n : Num) :
    (Computability.encodeNum n).length = n.natSize := by
  cases n with
  | zero => rfl
  | pos p => simpa [Computability.encodeNum, Num.natSize] using length_encodePosNum p

@[simp]
theorem length_encodeNat (n : ℕ) :
    (Computability.encodeNat n).length = n.size := by
  simpa [Computability.encodeNat, Num.natSize_to_nat] using
    length_encodeNum (n : Num)

@[simp]
theorem length_bitEncode (n : ℕ) :
    (bitEncode n).length = n.size := by
  rw [bitEncode_nat, length_encodeNat]

theorem bitEncode_pair_nat_length (x : ℕ × ℕ) :
    (bitEncode x).length = 2 * x.1.size + x.2.size + 1 := by
  change (delimit (Computability.encodeNat x.1) ++
    Computability.encodeNat x.2).length = _
  rw [List.length_append, length_delimit, length_encodeNat,
    length_encodeNat]
  omega

theorem bitEncode_pair_nat_length_le (x : ℕ × ℕ) :
    (bitEncode x).length ≤ 2 * (x.1.size + x.2.size) + 1 := by
  rw [bitEncode_pair_nat_length]
  omega

end MetaMathlibExt.BinaryNatEncoding
