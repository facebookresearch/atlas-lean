/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.BitEncoding
import Mathlib.Tactic.NormNum.Prime

/-! Tests for `MathlibExt.Data.BitEncoding`. -/

namespace MathlibExtTest.BitEncoding

/-! Big-endian layout: the head is the most significant bit. -/

example : Nat.toBitsBE 4 11 = [true, false, true, true] := by decide
example : Nat.toBitsBE 8 1 = [false, false, false, false, false, false, false, true] := by decide
example : Nat.ofBitsBE [true, false, true, true] = 11 := by decide
example : Nat.ofBitsBE [false, false, true, true] = 3 := by decide
example : Nat.ofBitsBE [] = 0 := by decide

/-! Truncation to the low `w` bits, and the general roundtrip `n % 2 ^ w`. -/

example : Nat.toBitsBE 3 11 = [false, true, true] := by decide
example : Nat.ofBitsBE (Nat.toBitsBE 3 11) = 3 := by
  rw [Nat.ofBitsBE_toBitsBE]; norm_num
example : Nat.ofBitsBE (Nat.toBitsBE 16 3233) = 3233 :=
  Nat.ofBitsBE_toBitsBE_of_lt (by norm_num)
example : Nat.ofBitsBE (Nat.toBitsBE (Nat.size 3233) 3233) = 3233 :=
  Nat.ofBitsBE_toBitsBE_size 3233
example : (Nat.toBitsBE 2048 3233).length = 2048 := Nat.length_toBitsBE _ _
example : Nat.toBitsBE [true, false, true].length (Nat.ofBitsBE [true, false, true]) =
    [true, false, true] :=
  Nat.toBitsBE_ofBitsBE _
example : Nat.ofBitsBE [true, true, true, true] < 2 ^ 4 := Nat.ofBitsBE_lt _

/-! The equivalence `Fin (2 ^ w) ≃ {l // l.length = w}`. -/

example : (Nat.bitsBEEquiv 4 ⟨13, by norm_num⟩).1 = [true, true, false, true] := by decide
example : ((Nat.bitsBEEquiv 4).symm ⟨[false, true, true, false], rfl⟩ : ℕ) = 6 := by decide

/-! `ZMod 23` with width `5` (`23 ≤ 32`). -/

example : ZMod.toBitsBE 5 (17 : ZMod 23) = [true, false, false, false, true] := by decide
example : ZMod.toBitsBE 5 (-1 : ZMod 23) = [true, false, true, true, false] := by decide
example : ((Nat.ofBitsBE (ZMod.toBitsBE 5 (17 : ZMod 23)) : ℕ) : ZMod 23) = 17 :=
  ZMod.ofBitsBE_toBitsBE (by norm_num) _
example : Nat.ofBitsBE (ZMod.toBitsBE 5 (-1 : ZMod 23)) = 22 := by
  rw [ZMod.ofBitsBE_toBitsBE_eq_val (by norm_num)]; rfl
example : Function.Injective (ZMod.toBitsBE (N := 23) 5) := ZMod.toBitsBE_injective (by norm_num)
example : ZMod.toBitsBE [true, false, true, false, true].length
    ((Nat.ofBitsBE [true, false, true, false, true] : ℕ) : ZMod 23) =
      [true, false, true, false, true] :=
  ZMod.toBitsBE_cast_ofBitsBE _ (by decide)

/-! Width `4` is too small for `ZMod 23`: `20` and `4` collide, so `N ≤ 2 ^ w` is needed. -/

example : ZMod.toBitsBE 4 (20 : ZMod 23) = ZMod.toBitsBE 4 (4 : ZMod 23) := by decide
example : (20 : ZMod 23) ≠ 4 := by decide

/-! `N = 0` satisfies `N ≤ 2 ^ w` at every width, but `ZMod 0 = ℤ` is infinite: `4` and `0`
collide at width `2`, so the `[NeZero N]` hypothesis is needed too. -/

example : (0 : ℕ) ≤ 2 ^ 2 := Nat.zero_le _
example : ZMod.toBitsBE 2 (4 : ZMod 0) = ZMod.toBitsBE 2 (0 : ZMod 0) := by decide
example : (4 : ZMod 0) ≠ 0 := by decide

/-! An RSA-sized modulus (`3233 = 61 · 53`) with width `12`. -/

example : ((Nat.ofBitsBE (ZMod.toBitsBE 12 (1234 : ZMod 3233)) : ℕ) : ZMod 3233) = 1234 :=
  ZMod.ofBitsBE_toBitsBE (by norm_num) _

end MathlibExtTest.BitEncoding
