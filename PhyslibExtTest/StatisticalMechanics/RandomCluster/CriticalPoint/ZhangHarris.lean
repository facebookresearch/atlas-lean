/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangHarris

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangHarris`

* `zih_criticalProbability_eq_half_of_faithful_exclusive` with every measurability hypothesis
  discharged, reduced to the exclusivity input `hexcl` (proved in `ZhangFaithfulExclusive`, which
  imports this module);
* `zih_percolationProbability_zero_of_matched_half` and `zih_fixedK_contradiction` in conditional
  form;
* `zih_sqrt_trick_left` at `k = N = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangHarris

open _root_.StatMech _root_.StatMech.TwoDim _root_.StatMech.Lattice _root_.StatMech.Percolation
open _root_.StatMech.Universality _root_.StatMech.RSW.Box
open scoped NNReal

-- `p_c = 1/2` from exclusivity alone.
example (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N) : criticalProbability 2 = (1 : ℝ) / 2 :=
  zih_criticalProbability_eq_half_of_faithful_exclusive hexcl
    (fun _ _ _ _ => measurableSet_horizontalCrossingEvent _ _ _ _)
    (fun _ _ => measurableSet_verticalCrossingEvent _ _ _ _)
    (fun _ _ => measurableSet_horizontalCrossingEvent _ _ _ _)

-- `θ(1/2) = 0` from the matched half bound.
example (hhalf : ∀ N : ℕ, halfMeasure.real (horizontalCrossingEvent
      (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    Universality.percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 :=
  zih_percolationProbability_zero_of_matched_half hhalf

-- Positive percolation and the matched bound are contradictory.
example (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2))
    (hhalf : ∀ N : ℕ, halfMeasure.real (horizontalCrossingEvent
      (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) : False :=
  zih_fixedK_contradiction hpos hhalf

-- The square-root trick for the left arm approximations.
example := zih_sqrt_trick_left 1 1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangHarris
