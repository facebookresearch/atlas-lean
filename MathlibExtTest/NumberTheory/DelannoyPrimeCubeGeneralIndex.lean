/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DelannoyHarmonicCongruence
import MathlibExt.NumberTheory.DelannoyPrimeCubeGeneralIndex

open Finset MathlibExt.NumberTheory.DelannoyTriangleWanted MetaMathlibExt

-- Evaluate the entries directly, without using `delannoy_mul_sub_one`.
example : (ordinaryRiordanPascalLikeMatrix 4 4 1 : ZMod 125) = 1 := by decide

example : (ordinaryRiordanPascalLikeMatrix 14 4 1 : ZMod 125) = 111 := by decide

example : (ordinaryRiordanPascalLikeMatrix 27 6 1 : ZMod 343) = 134 := by decide

-- The right-hand side also evaluates to the same residue in the noncentral case at p = 7.
example :
    1 + ((4 : ZMod 343) - 1) * 7 * (Int.fermatQuotient 7 (by decide) 2 (by decide) : ZMod 343) *
      (2 - 7 * (Int.fermatQuotient 7 (by decide) 2 (by decide) : ZMod 343)) = 134 := by decide

example : (∑ j ∈ range 4, harmonicMod 5 j * (2 : ZMod 5) ^ (j + 1) *
    ((j + 1 : ℕ) : ZMod 5)⁻¹) = 0 := by decide +kernel

example : (∑ j ∈ range 6, harmonicMod 7 j * (2 : ZMod 7) ^ (j + 1) *
    ((j + 1 : ℕ) : ZMod 7)⁻¹) = 0 := by decide +kernel
