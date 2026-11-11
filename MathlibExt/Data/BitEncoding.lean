/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Size

/-!
# Fixed-width big-endian bit encodings of `ℕ` and `ZMod N`

Cryptographic constructions move between integers and bit strings: padded RSA and RSA-OAEP
(Katz-Lindell, *Introduction to Modern Cryptography*, 2nd ed., §11.5) pad a message into a
bit string and read it as an element of `ℤ_N`, and keys are serialized as fixed-length strings.
This file gives a fixed-width encoding with exact roundtrip lemmas.

**Convention.** Encodings are *big-endian*: the head of the list is the most significant bit,
as in the integer/octet-string conversions of PKCS #1 (RFC 8017, I2OSP/OS2IP). A width-`w`
encoding of `n` keeps the low `w` bits of `n`, so it is lossless exactly when `n < 2 ^ w`. For
`ZMod N` this means a nonzero modulus `N` with `N ≤ 2 ^ w`.

## Main definitions

* `Nat.toBitsBE w n`: the `w`-bit big-endian encoding of `n` (of `n % 2 ^ w`).
* `Nat.ofBitsBE l`: the natural number with big-endian binary digits `l`, defined through
  Lean core's `BitVec.ofBoolListBE`.
* `Nat.bitsBEEquiv w`: `Fin (2 ^ w) ≃ {l : List Bool // l.length = w}`.
* `ZMod.toBitsBE w x`: the `w`-bit encoding of `x.val`.

## Main results

* `Nat.length_toBitsBE`, `Nat.ofBitsBE_lt`: length and range bounds.
* `Nat.ofBitsBE_toBitsBE` (`= n % 2 ^ w`), `Nat.ofBitsBE_toBitsBE_of_lt`,
  `Nat.toBitsBE_ofBitsBE`: the two roundtrips.
* `Nat.ofBitsBE_toBitsBE_size`: the minimal width `Nat.size n` is lossless.
* `ZMod.ofBitsBE_toBitsBE`, `ZMod.toBitsBE_injective`: the `ZMod N` encoding is lossless for a
  nonzero modulus `N` (`[NeZero N]`) with `N ≤ 2 ^ w`. Both hypotheses are needed: `N = 0`
  satisfies `N ≤ 2 ^ w` at every width, but `ZMod 0 = ℤ` is infinite while there are only `2 ^ w`
  strings of length `w`.
* `ZMod.toBitsBE_cast_ofBitsBE`: decode-then-encode for strings whose value is below `N`.

The variable-length binary encodings used for complexity classes live in
`MathlibExt.Computability.BinaryNatEncoding` and `MathlibExt.Computability.Complexity` (and the
open PR #8163 adds their `ℤ`, `ℚ` and `ℕ+` instances); those are not fixed-width and have no
`ZMod` version. The little-endian length field of Merkle–Damgård padding,
`Cslib.Crypto.MerkleDamgardPadding.encodeLength` / `decodeLength`, is defined as the reversal of
this codec.
-/

@[expose] public section

namespace Nat

/-- The `w`-bit big-endian encoding of `n`: bit `i` of the list is bit `w - 1 - i` of `n`. Only
the low `w` bits of `n` are kept. Used to serialize integers as fixed-length strings, e.g. in
padded RSA and RSA-OAEP (Katz-Lindell, 2nd ed., §11.5). -/
def toBitsBE (w n : ℕ) : List Bool :=
  List.ofFn fun i : Fin w => n.testBit (w - 1 - i)

/-- The natural number whose big-endian binary digits are `l` (the inverse of `Nat.toBitsBE`,
Katz-Lindell, 2nd ed., §11.5). It is Lean core's `BitVec.ofBoolListBE` read as a number. -/
def ofBitsBE (l : List Bool) : ℕ :=
  (BitVec.ofBoolListBE l).toNat

/-- The `w`-bit encoding has length exactly `w`. -/
@[simp]
theorem length_toBitsBE (w n : ℕ) : (toBitsBE w n).length = w := by
  simp [toBitsBE]

/-- Element `i` of `Nat.toBitsBE w n` is bit `w - 1 - i` of `n`. -/
theorem getElem_toBitsBE (w n i : ℕ) (h : i < (toBitsBE w n).length) :
    (toBitsBE w n)[i] = n.testBit (w - 1 - i) := by
  simp [toBitsBE]

/-- Bit `i` of `Nat.ofBitsBE l` is element `l.length - 1 - i` of `l` when `i < l.length`, and
`false` otherwise. -/
theorem testBit_ofBitsBE (l : List Bool) (i : ℕ) :
    (ofBitsBE l).testBit i = (decide (i < l.length) && l.getD (l.length - 1 - i) false) := by
  rw [ofBitsBE, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListBE]

/-- A big-endian list of length `w` decodes to a number below `2 ^ w`. -/
theorem ofBitsBE_lt (l : List Bool) : ofBitsBE l < 2 ^ l.length :=
  (BitVec.ofBoolListBE l).isLt

/-- **Encode-then-decode.** Decoding the `w`-bit encoding of `n` recovers `n % 2 ^ w`. -/
theorem ofBitsBE_toBitsBE (w n : ℕ) : ofBitsBE (toBitsBE w n) = n % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ofBitsBE, length_toBitsBE, Nat.testBit_mod_two_pow]
  by_cases hi : i < w
  · have hlt : w - 1 - i < (toBitsBE w n).length := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      getElem_toBitsBE]
    simp only [hi, decide_true, Bool.true_and]
    congr 1
    omega
  · simp [hi]

/-- **Encode-then-decode, lossless case.** If `n < 2 ^ w`, decoding the `w`-bit encoding of `n`
recovers `n`. -/
theorem ofBitsBE_toBitsBE_of_lt {w n : ℕ} (h : n < 2 ^ w) : ofBitsBE (toBitsBE w n) = n := by
  rw [ofBitsBE_toBitsBE, Nat.mod_eq_of_lt h]

/-- The minimal width `Nat.size n` encodes `n` losslessly. -/
theorem ofBitsBE_toBitsBE_size (n : ℕ) : ofBitsBE (toBitsBE n.size n) = n :=
  ofBitsBE_toBitsBE_of_lt (lt_size_self n)

/-- **Decode-then-encode.** Re-encoding the decoding of `l` at width `l.length` gives back `l`. -/
theorem toBitsBE_ofBitsBE (l : List Bool) : toBitsBE l.length (ofBitsBE l) = l := by
  apply List.ext_getElem (length_toBitsBE _ _)
  intro i h₁ h₂
  rw [getElem_toBitsBE, testBit_ofBitsBE]
  have hlt : l.length - 1 - (l.length - 1 - i) < l.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  simp only [show l.length - 1 - i < l.length by omega, decide_true, Bool.true_and]
  congr 1
  omega

/-- The `w`-bit encoding is injective on numbers below `2 ^ w`. -/
theorem toBitsBE_injOn (w : ℕ) : Set.InjOn (toBitsBE w) (Set.Iio (2 ^ w)) := by
  intro a ha b hb hab
  rw [← ofBitsBE_toBitsBE_of_lt ha, ← ofBitsBE_toBitsBE_of_lt hb, hab]

/-- Numbers below `2 ^ w` are in bijection with bit strings of length `w`, via the big-endian
encoding. -/
def bitsBEEquiv (w : ℕ) : Fin (2 ^ w) ≃ {l : List Bool // l.length = w} where
  toFun n := ⟨toBitsBE w n, length_toBitsBE _ _⟩
  invFun l := ⟨ofBitsBE l.1, lt_of_lt_of_eq (ofBitsBE_lt l.1) (by rw [l.2])⟩
  left_inv n := Fin.ext (ofBitsBE_toBitsBE_of_lt n.2)
  right_inv l := by
    obtain ⟨l, rfl⟩ := l
    exact Subtype.ext (toBitsBE_ofBitsBE l)

end Nat

namespace ZMod

variable {N : ℕ}

/-- The `w`-bit big-endian encoding of `x : ZMod N`, through its canonical representative
`x.val`. It is lossless when `N ≠ 0` and `N ≤ 2 ^ w` (`ZMod.ofBitsBE_toBitsBE`,
`ZMod.toBitsBE_injective`), e.g. for serializing elements of `ℤ_N` in RSA (Katz-Lindell, 2nd ed.,
§11.5). The bound alone is not enough: for `N = 0` it holds at every width, but `ZMod 0 = ℤ` is
infinite, so no fixed width is lossless. -/
def toBitsBE (w : ℕ) (x : ZMod N) : List Bool :=
  Nat.toBitsBE w x.val

/-- The `w`-bit encoding of an element of `ZMod N` has length `w`. -/
@[simp]
theorem length_toBitsBE (w : ℕ) (x : ZMod N) : (toBitsBE w x).length = w :=
  Nat.length_toBitsBE _ _

/-- **Encode-then-decode in `ZMod N`.** For a nonzero modulus `N` (`[NeZero N]`) with
`N ≤ 2 ^ w`, decoding the `w`-bit encoding of `x` and reducing modulo `N` recovers `x`. -/
theorem ofBitsBE_toBitsBE [NeZero N] {w : ℕ} (hN : N ≤ 2 ^ w) (x : ZMod N) :
    ((Nat.ofBitsBE (toBitsBE w x) : ℕ) : ZMod N) = x := by
  rw [toBitsBE, Nat.ofBitsBE_toBitsBE_of_lt (lt_of_lt_of_le x.val_lt hN), natCast_zmod_val]

/-- For a nonzero modulus `N` (`[NeZero N]`) with `N ≤ 2 ^ w`, the decoded value is the
canonical representative itself (no reduction needed). -/
theorem ofBitsBE_toBitsBE_eq_val [NeZero N] {w : ℕ} (hN : N ≤ 2 ^ w) (x : ZMod N) :
    Nat.ofBitsBE (toBitsBE w x) = x.val :=
  Nat.ofBitsBE_toBitsBE_of_lt (lt_of_lt_of_le x.val_lt hN)

/-- The `w`-bit encoding of `ZMod N` is injective for a nonzero modulus `N` (`[NeZero N]`) with
`N ≤ 2 ^ w`. Without `N ≠ 0` it fails: `ZMod 0 = ℤ` is infinite and has no injective fixed-width
encoding. -/
theorem toBitsBE_injective [NeZero N] {w : ℕ} (hN : N ≤ 2 ^ w) :
    Function.Injective (toBitsBE (N := N) w) := by
  intro x y h
  rw [← ofBitsBE_toBitsBE hN x, ← ofBitsBE_toBitsBE hN y, h]

/-- **Decode-then-encode in `ZMod N`.** A bit string whose value is below `N` survives the trip
through `ZMod N`. -/
theorem toBitsBE_cast_ofBitsBE (l : List Bool) (hl : Nat.ofBitsBE l < N) :
    toBitsBE l.length ((Nat.ofBitsBE l : ℕ) : ZMod N) = l := by
  rw [toBitsBE, val_natCast, Nat.mod_eq_of_lt hl, Nat.toBitsBE_ofBitsBE]

end ZMod
