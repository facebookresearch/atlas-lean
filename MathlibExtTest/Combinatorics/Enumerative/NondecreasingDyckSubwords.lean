/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.NondecreasingDyckSubwords

/-!
# Tests for subwords in non-decreasing Dyck paths

The empty path has no occurrences. Four consecutive up steps contain two overlapping triples.
-/

open MetaMathlibExt DyckStep

example : PowerSeries.coeff 0 (nondecreasingDyckSubwordBivariateGF [U, U, U]) = 0 := by
  simp [nondecreasingDyckSubwordBivariateGF]

example : nondecreasingDyckSubwordTotal [U, U, U] 0 = 0 := by decide +kernel

example : dyckSubwordCount [U, U, U] [U, U, U, U, D, D, D, D] = 2 := by decide

example : nondecreasingDyckSubwordTotal [U, U, U] 4 = 6 := by decide +kernel
