/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangFixedK

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangFixedK`

* `zfk_criticalProbability_eq_half_of_faithful_exclusive` with measurability discharged, reduced
  to positive association and exclusivity;
* `zfk_matched_half_of_faithful_exclusive` and `zfk_percolationProbability_zero_of_matched_half`
  in conditional form (the inputs are proved in `ZhangHarris`/`ZhangFaithfulExclusive`, which
  import this module);
* `zfk_armLower_tendsto_one` in conditional form (it assumes `θ(1/2) > 0`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangFixedK

open _root_.StatMech _root_.StatMech.TwoDim _root_.StatMech.Lattice _root_.StatMech.Universality
open _root_.StatMech.Percolation _root_.StatMech.RSW.Box Filter
open scoped NNReal

-- `p_c = 1/2` from positive association and exclusivity.
example (hpa : PositivelyAssociated halfMeasure) (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N) :
    criticalProbability 2 = (1 : ℝ) / 2 :=
  zfk_criticalProbability_eq_half_of_faithful_exclusive hpa hexcl
    (fun _ _ _ _ => measurableSet_horizontalCrossingEvent _ _ _ _)
    (fun _ _ => measurableSet_verticalCrossingEvent _ _ _ _)
    (fun _ _ => measurableSet_horizontalCrossingEvent _ _ _ _)

-- Exclusivity gives the matched bound at `N = 2`.
example (hexcl : zfk_FaithfulMatchedExclusive 2) :
    halfMeasure.real (horizontalCrossingEvent (-(2 : ℕ) : ℤ) ((2 : ℕ) + 1) (-(2 : ℕ) : ℤ) (2 : ℕ))
      ≤ (1 : ℝ) / 2 :=
  zfk_matched_half_of_faithful_exclusive 2 hexcl

-- `θ(1/2) = 0` from positive association and the matched bound.
example (hpa : PositivelyAssociated halfMeasure)
    (hhalf : ∀ N : ℕ, halfMeasure.real (horizontalCrossingEvent
      (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    Universality.percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 :=
  zfk_percolationProbability_zero_of_matched_half hpa hhalf

-- Conditional on percolation, the four-arm lower bound tends to `1`.
example (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    Tendsto zfk_armLower atTop (nhds 1) :=
  zfk_armLower_tendsto_one hpos

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangFixedK
