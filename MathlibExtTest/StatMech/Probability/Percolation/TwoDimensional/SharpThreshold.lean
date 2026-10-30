/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.SharpThreshold
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.SharpThreshold`

* `kst_theta_eq_zero_iff` and `kst_crossProb_tendsto_zero_of_theta_zero` at `p = 0`, where
  `θ = 0` is proved by `theta_eq_zero_of_lt`.
* `kst_subcriticalDensities_eq_coe`: `0` is a subcritical density.
* `kst_sharpThreshold_crossingEvent` / `kst_sharpThreshold_of_dominated` are not instantiated:
  their hypothesis `hsub` (`θ = 0` below `p_c`) needs monotonicity of `θ`, which the library
  lacks.
-/

@[expose] public section

open Filter MeasureTheory
open scoped NNReal Topology
open StatMech StatMech.Lattice StatMech.Percolation StatMech.TwoDim

namespace MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.SharpThreshold

theorem theta_zero : Percolation.theta 2 0 (zero_le_one) = 0 :=
  theta_eq_zero_of_lt (by norm_num) 0 zero_le_one (by norm_num)

example : Universality.percolationProbability 2 0 zero_le_one = 0 :=
  (kst_theta_eq_zero_iff 2 0 zero_le_one).mp theta_zero

example : Tendsto (fun n => Percolation.crossProb 2 0 zero_le_one n) atTop (𝓝 0) :=
  kst_crossProb_tendsto_zero_of_theta_zero 2 0 zero_le_one theta_zero

example : (0 : ℝ) ∈ Universality.subcriticalDensities 2 := by
  rw [kst_subcriticalDensities_eq_coe]
  exact ⟨0, ⟨zero_le_one, theta_zero⟩, rfl⟩

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.SharpThreshold
