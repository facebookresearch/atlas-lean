/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RamanujanTauModThree

open MetaMathlibExt

-- The first positive multiple of three is covered.
example : (3 : ℤ) ∣ generalizedTau 24 3 :=
  Int.modEq_zero_iff_dvd.mp (ramanujanTau_three_mul_modEq_zero 1 one_pos)

-- The divisibility does not extend to every positive index.
example : ¬ (3 : ℤ) ∣ generalizedTau 24 1 := by
  rw [generalizedTau_one]
  decide
