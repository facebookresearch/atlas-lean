/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ZModDifferenceBasis
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for difference bases modulo a prime -/

open MetaMathlibExt

-- At the smallest prime the two lists overlap, and zero still has a representation.
example : ∀ x : ZMod 2, 1 ≤ subRepCount ({0, 1} : Finset (ZMod 2)) x := by decide

-- Just above the square 16, the construction bounds the minimum by 10.
example : groupDiffBasisNumber 1 (ZMod 17) ≤ 10 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  calc
    _ ≤ 2 * ⌈Real.sqrt 17⌉₊ := groupDiffBasisNumber_zmod_le 17
    _ ≤ 2 * 5 := Nat.mul_le_mul_left 2 (Nat.ceil_le.mpr (Real.sqrt_le_iff.mpr (by norm_num)))
