/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing

/-! Tests: decay between events on a numeric window. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.Dosing

open MathlibExt.Biology.Biophysics.CompartmentKinetics.Dosing

/-- `tau = 2`, `t = 5` lies in window `n = 2`. -/
example : (∑ i ∈ Finset.range (⌊(5:ℝ) / 2⌋₊ + 1),
      3 * Real.exp (-(1:ℝ) * (5 - i * 2))) =
    Real.exp (-(1:ℝ) * (5 - 2 * 2)) *
      (∑ i ∈ Finset.range (2 + 1), 3 * Real.exp (-(1:ℝ) * (2 * 2 - i * 2))) :=
  periodic_amount_decay (by norm_num) (by norm_num) 2 (by rw [Nat.floor_eq_iff (by norm_num : (0:ℝ) ≤ 5 / 2)]; norm_num)

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.Dosing
