/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Infix
public import MathlibExt.Data.BitEncoding

/-!
# Bit-string padding for the Merkle–Damgård transform

A message is a bit string `M : List Bool`. Given a block length `B` and a length-field width `L`,
`pad B L M` appends a `1` bit, then the fewest `0` bits that make the total length a multiple of
`B`, then the `L`-bit encoding of `M.length`:

  `pad B L M = M ++ 1 0…0 ++ ⟨|M|⟩_L`.

* `pad_length_dvd`: if `0 < B`, the padded length is a multiple of `B`.
* `decodeLength_lengthField_pad`: if `|M| < 2 ^ L`, the last `L` bits of `pad B L M` decode to
  `|M|`, so the length field recovers the message length.
* `pad_injective`: padding is injective for every `B`, `L`, and message, with no length bound:
  removing the `L`-bit length field, the final `true` bit before the trailing `false` bits marks
  where the message ends. `pad_ne_of_length_ne` is the special case of messages of different
  lengths.
* `unpad_pad`: if `|M| < 2 ^ L`, `unpad` inverts `pad` by reading the length field.
* `lengthField_pad_ne_of_length_ne` and `encodeLength_injOn`: messages of different lengths below
  `2 ^ L` get different length fields; this is the bit-level form of the `lenBlock` separation
  hypothesis of `Cslib.Crypto.MerkleDamgard.findCollision_spec`.

Block alignment needs `0 < B`; decoding the length field (and hence `unpad`) needs `|M| < 2 ^ L`.
Injectivity needs neither. No relation between `B` and `L` is needed: the length field may share
the final block with the message bits.

**Relation to the textbook.** Katz and Lindell's Construction 5.3 zero-pads the message to a
multiple of the block length `n` and appends `|M| < 2 ^ n` as one extra block. The padding here is
the Merkle–Damgård strengthening used by SHA-2 (`1`, then `0`s, then the length), with the length
field width `L` a free parameter; taking `L = B` and putting the length in its own block gives the
textbook layout up to the `1` bit. Wave 2 connects `pad` to the block-list transform of
`CSLibExt.Crypto.Hash.MerkleDamgard` (full Construction 5.3); that file is untouched here.

The length is encoded little-endian (least significant bit first); the bit order does not affect
any statement. `encodeLength` and `decodeLength` are the reversals of the canonical fixed-width
big-endian codec `Nat.toBitsBE` / `Nat.ofBitsBE` of `MathlibExt.Data.BitEncoding`, and their
lemmas are derived from that codec's.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 5.2, Construction 5.3.
-/

@[expose] public section

namespace Cslib.Crypto.MerkleDamgardPadding

/-! ### The length field -/

/-- The `w`-bit little-endian encoding of `n`: least significant bit first, bits at positions
`≥ w` dropped. This is the length field `⟨L⟩` of Katz and Lindell, Construction 5.3, in a
configurable width. It is the reversal of the canonical big-endian codec `Nat.toBitsBE`. -/
def encodeLength (w n : ℕ) : List Bool := (Nat.toBitsBE w n).reverse

/-- Decode a little-endian bit string to a natural number: the canonical big-endian decoder
`Nat.ofBitsBE` applied to the reversed string. -/
def decodeLength (l : List Bool) : ℕ := Nat.ofBitsBE l.reverse

/-- The length field has exactly `w` bits. -/
@[simp]
theorem length_encodeLength (w n : ℕ) : (encodeLength w n).length = w := by
  simp [encodeLength]

/-- Decoding the `w`-bit encoding of `n` returns `n` modulo `2 ^ w`. -/
theorem decodeLength_encodeLength (w n : ℕ) : decodeLength (encodeLength w n) = n % 2 ^ w := by
  rw [decodeLength, encodeLength, List.reverse_reverse, Nat.ofBitsBE_toBitsBE]

/-- The `w`-bit encoding is injective on numbers below `2 ^ w`. -/
theorem encodeLength_injOn {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : encodeLength w a = encodeLength w b) : a = b :=
  Nat.toBitsBE_injOn w ha hb (List.reverse_injective h)

/-! ### Padding -/

variable (B L : ℕ)

/-- The number of `0` bits in the padding of a message of length `m`: the least `k` with
`B ∣ m + 1 + k + L`. -/
def numZeros (m : ℕ) : ℕ := (B - (m + 1 + L) % B) % B

/-- **Merkle–Damgård padding** (the strengthened variant of Katz and Lindell, Construction 5.3):
the message, a `1` bit, `numZeros B L |M|` zero bits, and the `L`-bit length field. -/
def pad (M : List Bool) : List Bool :=
  M ++ (true :: List.replicate (numZeros B L M.length) false) ++ encodeLength L M.length

/-- The length field of a padded string: its last `L` bits. -/
def lengthField (P : List Bool) : List Bool := P.drop (P.length - L)

/-- Recover a message from its padding: read the length `n` from the last `L` bits and keep the
first `n` bits. -/
def unpad (P : List Bool) : List Bool := P.take (decodeLength (lengthField L P))

/-- The padded length: message, one `1` bit, the zeros, and the length field. -/
theorem length_pad (M : List Bool) :
    (pad B L M).length = M.length + 1 + numZeros B L M.length + L := by
  simp [pad]
  omega

/-- The message is a prefix of its padding. -/
theorem prefix_pad (M : List Bool) : M <+: pad B L M := by
  rw [pad, List.append_assoc]
  exact List.prefix_append _ _

/-- **Block alignment**: for a positive block length, the padded length is a multiple of `B`. -/
theorem pad_length_dvd (hB : 0 < B) (M : List Bool) : B ∣ (pad B L M).length := by
  rw [length_pad, numZeros]
  set x := M.length + 1 + L
  have hx : M.length + 1 + (B - x % B) % B + L = x + (B - x % B) % B := by omega
  rw [hx]
  have hr : x % B < B := Nat.mod_lt _ hB
  have hle : x % B ≤ x := Nat.mod_le _ _
  by_cases h0 : x % B = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    exact Nat.dvd_of_mod_eq_zero h0
  · rw [Nat.mod_eq_of_lt (by omega : B - x % B < B)]
    have : x + (B - x % B) = (x - x % B) + B := by omega
    rw [this]
    exact Nat.dvd_add (Nat.dvd_sub_mod x) (Nat.dvd_refl B)

/-- The length field of `pad B L M` is the `L`-bit encoding of `|M|`. -/
theorem lengthField_pad (M : List Bool) :
    lengthField L (pad B L M) = encodeLength L M.length := by
  rw [lengthField, pad]
  exact List.drop_left' (by simp; omega)

/-- **Length recovery**: if `|M| < 2 ^ L`, the length field of `pad B L M` decodes to `|M|`. -/
theorem decodeLength_lengthField_pad {M : List Bool} (hM : M.length < 2 ^ L) :
    decodeLength (lengthField L (pad B L M)) = M.length := by
  rw [lengthField_pad, decodeLength_encodeLength, Nat.mod_eq_of_lt hM]

/-- `unpad` inverts `pad` on messages of length below `2 ^ L`. -/
theorem unpad_pad {M : List Bool} (hM : M.length < 2 ^ L) : unpad L (pad B L M) = M := by
  rw [unpad, decodeLength_lengthField_pad B L hM, pad, List.append_assoc]
  exact List.take_left

/-- The number of leading `false` bits and the rest of the list after the first `true` are
determined by the list. -/
theorem replicate_false_append_true_inj : ∀ {a b : ℕ} {s t : List Bool},
    List.replicate a false ++ true :: s = List.replicate b false ++ true :: t → a = b ∧ s = t
  | 0, 0, _, _, h => by simpa using h
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, _ + 1, _, _, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := replicate_false_append_true_inj h
    exact ⟨rfl, rfl⟩

/-- **Padding is injective** for every block length `B`, length-field width `L`, and message, with
no bound on the message length (Katz and Lindell, Construction 5.3: distinct inputs give distinct
padded strings). Dropping the `L`-bit length field leaves `M ++ 1 0…0`, and the last `1` bit marks
the end of `M`; the length field is not read, so `|M| ≥ 2 ^ L` is allowed. -/
theorem pad_injective : Function.Injective (pad B L) := by
  intro M M' h
  have hcore : M ++ true :: List.replicate (numZeros B L M.length) false =
      M' ++ true :: List.replicate (numZeros B L M'.length) false :=
    List.append_inj_left' h (by simp)
  have hrev := congrArg List.reverse hcore
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append] at hrev
  exact List.reverse_inj.1 (replicate_false_append_true_inj hrev).2

/-- **Length separation**: messages of different lengths below `2 ^ L` have different length
fields, hence different padded strings. This is the bit-level counterpart of the hypothesis
`lenBlock M.length = lenBlock M'.length → M.length = M'.length` of
`Cslib.Crypto.MerkleDamgard.findCollision_spec`. -/
theorem lengthField_pad_ne_of_length_ne {M M' : List Bool} (hM : M.length < 2 ^ L)
    (hM' : M'.length < 2 ^ L) (hne : M.length ≠ M'.length) :
    lengthField L (pad B L M) ≠ lengthField L (pad B L M') := by
  rw [lengthField_pad, lengthField_pad]
  exact fun h => hne (encodeLength_injOn hM hM' h)

/-- Messages of different lengths have different padded strings, for every length (a corollary of
`pad_injective`; the length fields may coincide when a length is at least `2 ^ L`). -/
theorem pad_ne_of_length_ne {M M' : List Bool} (hne : M.length ≠ M'.length) :
    pad B L M ≠ pad B L M' :=
  fun h => hne (congrArg List.length (pad_injective B L h))

end Cslib.Crypto.MerkleDamgardPadding
