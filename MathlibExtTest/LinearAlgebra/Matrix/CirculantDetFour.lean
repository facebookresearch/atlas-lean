/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.CirculantDetFour
import Mathlib.Tactic.NormNum

/-!
# Tests for the four-by-four circulant determinant
-/

open MetaMathlibExt

-- Distinct integer entries give a negative determinant.
example : circulantDetFour ![(1 : ℤ), 2, 3, 4] = -160 := by
  rw [circulantDetFour_eq]
  norm_num

-- When opposite entries coincide, the matrix has two pairs of equal rows.
example {R : Type*} [CommRing R] (a b : R) : circulantDetFour ![a, b, a, b] = 0 := by
  simp [circulantDetFour_eq]
