/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.Hash.Sponge
import Mathlib.Data.List.Rotate

/-!
# Permutation sponge examples

With rate two, capacity one, and the left rotation `(a,b,c) ↦ (b,c,a)`, absorbing `11` into
`000` gives `101`. Reading before each subsequent rotation gives rate chunks `10`, `01`, `11`:
the three- and five-bit outputs are `100` and `10011`. These finite examples exercise the
generic construction, not a concrete Keccak permutation or a SHA-3 test vector.
-/

namespace Cslib.Crypto.Sponge.Tests

private abbrev Bits (n : ℕ) := List.Vector Bool n

private def rot (n : ℕ) (s : Bits 3) : Bits 3 :=
  ⟨s.toList.rotate n, by simp [List.Vector.toList_length]⟩

private def cycle : Equiv.Perm (Bits 3) where
  toFun := rot 1
  invFun := rot 2
  left_inv s := by
    apply List.Vector.toList_injective
    change (s.toList.rotate 1).rotate 2 = s.toList
    rw [List.rotate_rotate]
    simpa only [List.Vector.toList_length] using List.rotate_length s.toList
  right_inv s := by
    apply List.Vector.toList_injective
    change (s.toList.rotate 2).rotate 1 = s.toList
    rw [List.rotate_rotate]
    simpa only [List.Vector.toList_length] using List.rotate_length s.toList

private def ones : Bits 2 := ⟨[true, true], rfl⟩
private def lastBit : Bits 2 := ⟨[false, true], rfl⟩
private def toy (ps : List (Bits 2)) (d : ℕ) := output (c := 1) cycle (by decide) ps d

-- A non-palindromic state, asymmetric block and set capacity bit, before permutation.
example : (mix (c := 1) ⟨[false, true, true], rfl⟩ lastBit).toList = [false, false, true] := rfl

-- The two absorbs do not commute; a later block encounters a nonzero chaining state.
example : (absorb (c := 1) cycle ⟨[false, false, false], rfl⟩ [ones, lastBit]).toList =
    [true, true, true] := rfl
example : (absorb (c := 1) cycle ⟨[false, false, false], rfl⟩ [lastBit, ones]).toList =
    [true, false, false] := rfl

example : toy [ones] 0 = [] := by rw [toy, output, squeeze_of_le _ _ _ (by decide), List.take_zero]
example : toy [ones] 1 = [true] := by rw [toy, output, squeeze_of_le _ _ _ (by decide)]; rfl
example : toy [ones] 2 = [true, false] := by rw [toy, output, squeeze_of_le _ _ _ (by decide)]; rfl
example : toy [ones] 3 = [true, false, false] := by
  rw [toy, output, squeeze_add_rate (r := 2) (c := 1) _ _ _ 1, squeeze_of_le _ _ _ (by decide)]
  rfl
example : toy [ones] 4 = [true, false, false, true] := by
  rw [toy, output, squeeze_add_rate (r := 2) (c := 1) _ _ _ 2, squeeze_of_le _ _ _ (by decide)]
  rfl
example : toy [ones] 5 = [true, false, false, true, true] := by
  rw [toy, output, squeeze_add_rate (r := 2) (c := 1) _ _ _ 3,
    squeeze_add_rate (r := 2) (c := 1) _ _ _ 1, squeeze_of_le _ _ _ (by decide)]
  rfl

-- Empty block input is the fold identity, not the padding of the empty raw message.
example : toy [] 2 = [false, false] := by rw [toy, output, squeeze_of_le _ _ _ (by decide)]; rfl
example : (pad10star1 2 (by decide)).blocks [] = [ones] := by decide
example : (pad10star1 2 (by decide)).blocks [false] = [lastBit, lastBit] := by decide

-- When the two ends just fit, insert no zeros; with one free lane, cross a block boundary.
example : (pad10star1 4 (by decide)).suffix 2 = [true, true] := rfl
example : (pad10star1 4 (by decide)).suffix 3 = [true, false, false, false, true] := rfl
example : (pad10star1 1 (by decide)).suffix 0 = [true, true] := rfl

end Cslib.Crypto.Sponge.Tests
