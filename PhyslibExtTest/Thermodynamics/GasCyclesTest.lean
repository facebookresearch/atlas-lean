/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Thermodynamics.GasCycles

import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Thermodynamics.GasCycles`

A freezer between `250 K` and `300 K` that absorbs `4000 J` per cycle for `1000 J` of work:

* its Clausius residual is `2/3 J/K` and both coefficients of performance lie strictly below the
  reversible bounds `5` and `6`;
* the general results apply to it: the Clausius inequality forces positive work, the bounds hold,
  and the reversible machine (`5000 J` absorbed, `6000 J` rejected) attains them.
-/

@[expose] public section

namespace PhyslibExtTest.Thermodynamics.GasCycles

open _root_.GasCycles

-- Fixture: a freezer between `Tc = 250` K and `Th = 300` K absorbs `Qc = 4000` J and takes
-- `W = 1000` J, rejecting `Qh = 5000` J. Its Clausius residual is `2/3` J/K, and
-- `COP_R = 4 < 5 = Tc / (Th - Tc)`, `COP_HP = 5 < 6 = Th / (Th - Tc)`. The reversible machine with
-- `Qc = 5000` J and `Qh = 6000` J has zero residual and attains both bounds.
example :
    (5000 : ℝ) / 300 - 4000 / 250 = 2 / 3 ∧ (4000 : ℝ) / 1000 < 250 / (300 - 250) ∧
      (5000 : ℝ) / 1000 < 300 / (300 - 250) ∧ (6000 : ℝ) / 300 - 5000 / 250 = 0 ∧
      (5000 : ℝ) / 1000 = 250 / (300 - 250) ∧ (6000 : ℝ) / 1000 = 300 / (300 - 250) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

-- The freezer and the reversible machine through the general results: the Clausius inequality
-- forces positive work, both coefficients of performance obey the reversible bounds, and the
-- reversible machine attains the refrigerator bound because its Clausius residual is zero.
example :
    (0 : ℝ) < 1000 ∧
      ((4000 : ℝ) / 1000 ≤ 250 / (300 - 250) ∧ (5000 : ℝ) / 1000 ≤ 300 / (300 - 250)) ∧
      (5000 : ℝ) / 1000 = 250 / (300 - 250) := by
  refine ⟨work_pos_of_clausius (Qh := 5000) (Qc := 4000) (Tc := 250) (Th := 300)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cop_le_carnot (Qh := 5000) (Qc := 4000) (W := 1000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), ?_⟩
  exact (cop_eq_carnot_iff (Qh := 6000) (Qc := 5000) (W := 1000) (Tc := 250) (Th := 300)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1.2 (by norm_num)

end PhyslibExtTest.Thermodynamics.GasCycles
