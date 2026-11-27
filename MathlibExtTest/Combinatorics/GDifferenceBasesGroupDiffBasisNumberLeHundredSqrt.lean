/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GDifferenceBasesGroupDiffBasisNumberLeHundredSqrt
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for the square-root bound for difference bases of finite fields -/

namespace MathlibExtTest.Combinatorics.GDifferenceBases

open MetaMathlibExt

-- The bound instantiated on the smallest odd field.
example : (groupDiffBasisNumber 1 (ZMod 3) : ℝ) ≤ 100 * Real.sqrt (Nat.card (ZMod 3)) :=
  groupDiffBasisNumber_le_hundred_sqrt

-- The exact value on Z/3, pinning what the bound constrains.
example : groupDiffBasisNumber 1 (ZMod 3) = 2 :=
  groupDiffBasisNumber_one_zmod_three

-- The exact value satisfies the bound: 2 ≤ 100√3.
example : (2 : ℝ) ≤ 100 * Real.sqrt (Nat.card (ZMod 3)) := by
  have : NeZero (3 : ℕ) := ⟨by norm_num⟩
  rw [Nat.card_eq_fintype_card, ZMod.card]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((3 : ℕ) : ℝ) := by
    rw [Real.le_sqrt zero_le_one (Nat.cast_nonneg _)]
    norm_num
  linarith [hsqrt]

noncomputable instance : DecidableEq (GaloisField 2 2) := Classical.decEq _

-- The bound instantiated on a non-prime field with four elements.
example : (groupDiffBasisNumber 1 (GaloisField 2 2) : ℝ) ≤
    100 * Real.sqrt (Nat.card (GaloisField 2 2)) :=
  groupDiffBasisNumber_le_hundred_sqrt

-- Corollary: on GF(4) the bound evaluates to η₁ ≤ 200.
example : (groupDiffBasisNumber 1 (GaloisField 2 2) : ℝ) ≤ 200 := by
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h := groupDiffBasisNumber_le_hundred_sqrt (K := GaloisField 2 2)
  rw [hcard] at h
  have h4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 from by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h4] at h
  linarith

end MathlibExtTest.Combinatorics.GDifferenceBases
