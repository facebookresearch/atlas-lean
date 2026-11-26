/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Probability.Percolation.Universality.RotatedDualCounterexamples
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.BXPMinimalHyp

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.BXPMinimalHyp`

* `bmh_square_seed_half_faithful` and `bmh_band_seed_half_faithful` at `n = 1` and `n = 5`, with
  every measurability hypothesis discharged (crossing events are rectangle-determined), so the
  square-crossing bound `1/2 ≤ P(cross)` holds unconditionally;
* `bmh_square_reflection` at `n = 3`;
* the headline `bmh_boxCrossingProperty_selfDual_faithful` reduced to its two genuine inputs
  (positive association and the `2n × n` RSW bound), measurability supplied.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.BXPMinimalHyp

open _root_.StatMech _root_.StatMech.Universality _root_.StatMech.Lattice
open _root_.StatMech.RSW.Box _root_.StatMech.RSW.Strip

/-- The square-crossing seed at `p = 1/2`, unconditionally. -/
theorem square_seed (n : ℤ) (hn : 0 < n) : (1 : ℝ) / 2 ≤ rai_cross halfMeasure n 1 :=
  bmh_square_seed_half_faithful n hn (RSW.Box.measurableSet_horizontalCrossingEvent _ _ _ _)
    (RSW.Box.measurableSet_verticalCrossingEvent _ _ _ _) (RSW.Box.measurableSet_horizontalCrossingEvent _ _ _ _)

-- The square seed at `n = 1`.
example : (1 : ℝ) / 2 ≤ rai_cross halfMeasure 1 1 := square_seed 1 one_pos

-- The band seed at `n = 5`.
example : (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 5 0 5) :=
  bmh_band_seed_half_faithful 5 (by norm_num) (RSW.Box.measurableSet_horizontalCrossingEvent _ _ _ _)
    (RSW.Box.measurableSet_verticalCrossingEvent _ _ _ _) (RSW.Box.measurableSet_horizontalCrossingEvent _ _ _ _)

-- Reflection: vertical and horizontal square crossings have equal probability.
example : halfMeasure.real (verticalCrossingEvent 0 3 0 3)
    = halfMeasure.real (horizontalCrossingEvent 0 3 0 3) :=
  bmh_square_reflection 3 (RSW.Box.measurableSet_horizontalCrossingEvent _ _ _ _)

-- BXP at every aspect ratio from positive association and the RSW `2n × n` bound alone.
example (hpa : PositivelyAssociated halfMeasure)
    (h2box : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 8 ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n)) :
    BoxCrossingProperty halfMeasure 2 :=
  bmh_boxCrossingProperty_selfDual_faithful hpa
    (fun _ _ _ _ => RSW.Box.measurableSet_horizontalCrossingEvent _ _ _ _)
    (fun _ _ _ _ => RSW.Box.measurableSet_verticalCrossingEvent _ _ _ _)
    (fun _ _ => RSW.Box.measurableSet_verticalCrossingEvent _ _ _ _)
    (fun _ _ => RSW.Box.measurableSet_horizontalCrossingEvent _ _ _ _) h2box 2 one_lt_two

/-- The old same-box separation premise for every positive square size fails at size two. -/
theorem no_all_positive_square_separation :
    ¬ (∀ n : ℤ, 0 < n →
      (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) := by
  intro hsep
  apply bcc_dichotomy_false
  exact hsep 2 (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.BXPMinimalHyp
