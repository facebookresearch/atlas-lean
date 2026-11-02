/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.KestenBXP

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.KestenBXP`

* `kbw_criticalProbability_le_half_square_faithful` with all measurability hypotheses discharged:
  `p_c(ℤ²) ≤ 1/2` unconditionally;
* `kbw_kesten_square_faithful` reduced to its three genuine inputs (positive association, the RSW
  `2n × n` bound and `BXP → θ(1/2) = 0`), measurability supplied;
* `kbw_halfMeasure_eq_rba` (now `rfl`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.KestenBXP

open _root_.StatMech _root_.StatMech.Universality _root_.StatMech.Lattice
open _root_.StatMech.RSW.Box
open scoped NNReal

-- Kesten's upper bound `p_c ≤ 1/2`, with no remaining hypotheses.
example : criticalProbability 2 ≤ 1 / 2 :=
  kbw_criticalProbability_le_half_square_faithful
    (fun _ _ _ _ => measurableSet_horizontalCrossingEvent _ _ _ _)
    (fun _ _ => measurableSet_verticalCrossingEvent _ _ _ _)
    (fun _ _ => measurableSet_horizontalCrossingEvent _ _ _ _)

-- `p_c = 1/2` from the three genuine inputs.
example (hpa : PositivelyAssociated halfMeasure)
    (h2box : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 8 ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hCor : BoxCrossingProperty halfMeasure 2 →
      percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0) :
    criticalProbability 2 = 1 / 2 :=
  kbw_kesten_square_faithful hpa
    (fun _ _ _ _ => measurableSet_horizontalCrossingEvent _ _ _ _)
    (fun _ _ _ _ => measurableSet_verticalCrossingEvent _ _ _ _)
    (fun _ _ => measurableSet_verticalCrossingEvent _ _ _ _)
    (fun _ _ => measurableSet_horizontalCrossingEvent _ _ _ _) h2box hCor

-- The continuity lemma is reflexivity.
example : halfMeasure = halfMeasure := kbw_halfMeasure_eq_rba

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.KestenBXP
