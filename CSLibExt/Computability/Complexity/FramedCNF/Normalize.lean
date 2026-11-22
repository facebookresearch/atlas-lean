/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding

/-!
# Normalizing the total binary natural-number decoder

Mathlib's decoder supplies an implicit most-significant one when a
nonempty payload ends in `false`. Normalization therefore appends a one;
it does not discard zeros or reject the payload.
-/

@[expose] public section

namespace Cslib.Complexity.FramedCNF

open Computability

/-- Canonicalize a raw payload without enumerating its decoded value. -/
def normalizeNat (bits : List Bool) : List Bool :=
  if bits.getLast? = some false then bits ++ [true] else bits

private theorem encode_decode_pos (bits : List Bool) :
    encodePosNum (decodePosNum bits) =
      if bits.getLast? = some true then bits else bits ++ [true] := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases bits with
    | nil => cases b <;> rfl
    | cons c rest =>
      cases b <;>
        simp only [decodePosNum, List.cons_ne_nil, ↓reduceIte,
          encodePosNum, List.getLast?_cons_cons, ih]
      all_goals split_ifs <;> rfl

/-- Normalization agrees with the existing total decoder on every
payload, not just canonical encodings. -/
theorem normalizeNat_eq_encode_decode (bits : List Bool) :
    normalizeNat bits = encodeNat (decodeNat bits) := by
  have h : encodeNat (decodeNat bits) = encodeNum (decodeNum bits) := by
    simp only [encodeNat, decodeNat, Num.of_to_nat]
  rw [h]
  cases bits with
  | nil => rfl
  | cons b bs =>
    simp only [decodeNum, List.cons_ne_nil, ↓reduceIte,
      PosNum.cast_to_num, encodeNum, encode_decode_pos]
    cases hl : (b :: bs).getLast? with
    | none => simp at hl
    | some c => cases c <;> simp [normalizeNat, hl]

/-- Normalization adds at most one bit. -/
theorem length_normalizeNat_le (bits : List Bool) :
    (normalizeNat bits).length ≤ bits.length + 1 := by
  unfold normalizeNat
  split_ifs <;> simp

/-- Canonical encodings are unchanged. -/
@[simp] theorem normalizeNat_encodeNat (n : ℕ) :
    normalizeNat (encodeNat n) = encodeNat n := by
  rw [normalizeNat_eq_encode_decode, decode_encodeNat]

end Cslib.Complexity.FramedCNF
