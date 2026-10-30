/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.ZhangLowerBound
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.ZhangLowerBound`

* `kzh_theta_real` (definitional) and `kzh_percProb_eq_zero_of_thetaReal_zero`.
* The headline `kzh_corLowerBound` and `kzh_crossing_to_one_of_union` are not instantiated:
  both take `PositivelyAssociated halfMeasure` (the Harris–FKG inequality for the infinite
  Bernoulli product), which the library does not prove for all increasing events.
-/

@[expose] public section

open Filter MeasureTheory
open scoped NNReal Topology
open StatMech StatMech.Lattice StatMech.Universality StatMech.TwoDim

namespace MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.ZhangLowerBound

example : (percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one).toReal
    = halfMeasure.real (percolationEvent 2) := kzh_theta_real

example (h : halfMeasure.real (percolationEvent 2) = 0) :
    percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 :=
  kzh_percProb_eq_zero_of_thetaReal_zero h

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.ZhangLowerBound
