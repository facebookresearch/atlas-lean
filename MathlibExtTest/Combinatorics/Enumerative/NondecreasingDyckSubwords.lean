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

The tests cover overlapping triples, valley-free paths, and peak and valley totals by semilength.
-/

open MetaMathlibExt DyckStep

example : PowerSeries.coeff 0 (nondecreasingDyckSubwordBivariateGF [U, U, U]) = 0 := by
  simp [nondecreasingDyckSubwordBivariateGF]

example : nondecreasingDyckSubwordTotal [U, U, U] 0 = 0 := by decide +kernel

example : dyckSubwordCount [U, U, U] [U, U, U, U, D, D, D, D] = 2 := by decide

example : nondecreasingDyckSubwordTotal [U, U, U] 4 = 6 := by decide +kernel

example : nondecreasingDyckSubwordTotal [D, U] 1 = 0 := by decide +kernel

-- The alternating path contributes two valleys at semilength three.
example : ((nondecreasingDyckWords 3).filter fun p =>
    dyckSubwordCount [D, U] p.val.toList = 2).card = 1 := by decide +kernel

-- Semilength four is the first at which the non-decreasing restriction removes a path.
example : nondecreasingDyckSubwordTotal [D, U] 4 = 19 := by decide +kernel

example : PowerSeries.coeff 0 (nondecreasingDyckSubwordBivariateGF [U, D]) = 0 := by
  simp [nondecreasingDyckSubwordBivariateGF]

example : nondecreasingDyckSubwordTotal [U, D] 0 = 0 := by decide +kernel

example : nondecreasingDyckSubwordTotal [U, D] 1 = 1 := by decide +kernel

-- Check the last initial value and the first value governed by the homogeneous recurrence.
example : nondecreasingDyckSubwordTotal [U, D] 4 = 32 := by decide +kernel

example : nondecreasingDyckSubwordTotal [U, D] 5 = 99 := by decide +kernel
