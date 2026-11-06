/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all Init.Data.Nat.Bitwise.Basic

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22QuadraticData

/-! Bounded ordinary kernel checks of all coefficient evaluation rows and inverse witnesses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem cacheBlock0 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨0 * 11 + j.val, by
      omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨0 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨0 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock1 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨1 * 11 + j.val, by
      omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨1 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨1 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock2 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨2 * 11 + j.val, by
      omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨2 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨2 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock3 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨3 * 11 + j.val, by
      omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨3 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨3 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock4 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨4 * 11 + j.val, by
      omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨4 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨4 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock5 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨5 * 11 + j.val, by
      omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨5 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨5 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock6 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨6 * 11 + j.val, by
      omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨6 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨6 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock7 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨7 * 11 + j.val, by
      omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨7 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨7 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock8 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨8 * 11 + j.val, by
      omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨8 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨8 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock9 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨9 * 11 + j.val, by
      omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨9 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨9 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock10 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨10 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨10 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨10 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock11 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨11 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨11 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨11 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock12 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨12 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨12 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨12 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock13 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨13 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨13 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨13 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock14 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨14 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨14 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨14 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock15 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨15 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨15 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨15 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock16 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨16 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨16 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨16 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock17 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨17 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨17 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨17 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock18 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨18 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨18 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨18 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock19 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨19 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨19 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨19 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock20 : ∀ j : Fin 11,
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨20 * 11 + j.val,
      by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨20 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨20 * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  decide +kernel

private theorem cacheBlock_all (h : Fin 21) (j : Fin 11) :
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks (⟨h.val * 11 +
      j.val, by omega⟩ : Fin 231)) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨h.val * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11)
      (co1ResidueM22LinearCoordinates (⟨h.val * 11 + j.val, by omega⟩ : Fin 231))
          (co1ResidueM22QuadraticTerms k).2 := by
  fin_cases h
  · exact cacheBlock0 j
  · exact cacheBlock1 j
  · exact cacheBlock2 j
  · exact cacheBlock3 j
  · exact cacheBlock4 j
  · exact cacheBlock5 j
  · exact cacheBlock6 j
  · exact cacheBlock7 j
  · exact cacheBlock8 j
  · exact cacheBlock9 j
  · exact cacheBlock10 j
  · exact cacheBlock11 j
  · exact cacheBlock12 j
  · exact cacheBlock13 j
  · exact cacheBlock14 j
  · exact cacheBlock15 j
  · exact cacheBlock16 j
  · exact cacheBlock17 j
  · exact cacheBlock18 j
  · exact cacheBlock19 j
  · exact cacheBlock20 j


/-- Every coefficient-mask row is exactly the actual quadratic monomial evaluation row. -/
theorem co1ResidueM22QuadraticMasks_correct (i : Fin 231) :
    monsterCo1GeometryBinaryMaskDecode (n := 66) (co1ResidueM22QuadraticMasks i) =
      fun k =>
        monsterCo1GeometryBinaryMaskDecode (n := 11) (co1ResidueM22LinearCoordinates i)
          (co1ResidueM22QuadraticTerms k).1 *
        monsterCo1GeometryBinaryMaskDecode (n := 11) (co1ResidueM22LinearCoordinates i)
          (co1ResidueM22QuadraticTerms k).2 := by
  let h : Fin 21 := ⟨i.val / 11, by omega⟩
  let j : Fin 11 := ⟨i.val % 11, Nat.mod_lt _ (by decide)⟩
  have he : (⟨h.val * 11 + j.val, by dsimp [h, j]; omega⟩ : Fin 231) = i := by
    apply Fin.ext
    dsimp [h, j]
    omega
  have ht := cacheBlock_all h j
  rwa [he] at ht

private theorem inverseBlock0 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨0 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨0 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock1 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨1 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨1 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock2 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨2 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨2 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock3 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨3 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨3 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock4 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨4 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨4 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock5 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨5 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨5 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock6 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨6 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨6 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock7 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨7 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨7 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock8 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨8 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨8 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock9 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨9 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨9 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock10 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨10 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨10 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock11 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨11 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨11 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock12 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨12 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨12 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock13 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨13 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨13 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock14 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨14 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨14 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock15 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨15 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨15 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock16 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨16 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨16 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock17 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨17 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨17 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock18 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨18 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨18 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock19 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨19 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨19 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock20 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨20 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨20 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock21 : ∀ j : Fin 3,
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨21 * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ ((⟨21 * 3 + j.val, by omega⟩ : Fin 66)).val := by
  decide +kernel

private theorem inverseBlock_all (h : Fin 22) (j : Fin 3) :
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow (⟨h.val * 3 + j.val, by omega⟩ : Fin 66)).map
        co1ResidueM22QuadraticMasks) =
        2 ^ (⟨h.val * 3 + j.val, by omega⟩ : Fin 66).val := by
  fin_cases h
  · exact inverseBlock0 j
  · exact inverseBlock1 j
  · exact inverseBlock2 j
  · exact inverseBlock3 j
  · exact inverseBlock4 j
  · exact inverseBlock5 j
  · exact inverseBlock6 j
  · exact inverseBlock7 j
  · exact inverseBlock8 j
  · exact inverseBlock9 j
  · exact inverseBlock10 j
  · exact inverseBlock11 j
  · exact inverseBlock12 j
  · exact inverseBlock13 j
  · exact inverseBlock14 j
  · exact inverseBlock15 j
  · exact inverseBlock16 j
  · exact inverseBlock17 j
  · exact inverseBlock18 j
  · exact inverseBlock19 j
  · exact inverseBlock20 j
  · exact inverseBlock21 j


/-- Selected original point evaluations span all sixty-six quadratic coefficient functionals. -/
theorem co1ResidueM22QuadraticInverse_correct (k : Fin 66) :
    monsterCo1GeometryBinaryMaskSum
      ((co1ResidueM22QuadraticInverseRow k).map co1ResidueM22QuadraticMasks) =
        2 ^ (k).val := by
  let h : Fin 22 := ⟨k.val / 3, by omega⟩
  let j : Fin 3 := ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩
  have he : (⟨h.val * 3 + j.val, by dsimp [h, j]; omega⟩ : Fin 66) = k := by
    apply Fin.ext
    dsimp [h, j]
    omega
  have ht := inverseBlock_all h j
  rwa [he] at ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
