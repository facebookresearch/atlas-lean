/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectAbundancySurplus

open MetaMathlibExt MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- The least prime factor may attain the lower endpoint 11.
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (hmin : n.minFac = 11) :
    (abundancySup n : ℝ) - 2 < 25 / (8 * 11 * Real.log 11) := by
  have h11 : 11 ≤ n.minFac := hmin.ge
  simpa only [hmin, Nat.cast_ofNat] using oddPerfect_abundancySup_sub_two_lt n hodd hperf h11

-- Equivalently, the bound controls the original prime product.
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h11 : 11 ≤ n.minFac) :
    (abundancySup n : ℝ) < 2 + 25 / (8 * (n.minFac : ℝ) * Real.log n.minFac) := by
  simpa only [add_comm] using
    (sub_lt_iff_lt_add.mp (oddPerfect_abundancySup_sub_two_lt n hodd hperf h11))
