/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.KestenCrossingDecay
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.KestenCrossingDecay`

* `kcd_horizontal_sharpThreshold` at `p = 0` (below `p_c(2) > 0`, by `pc_pos`): the square
  crossing probability tends to `0`. This headline is unconditional.
* `kcd_localOneArm_prob`, `kcd_crossProb_mono_param` (`p = 0 ≤ q = 1`),
  `kcd_quadratic_mul_exp_tendsto_zero` (`c = C = 1`).
-/

@[expose] public section

open Filter MeasureTheory
open scoped NNReal Topology
open StatMech StatMech.Lattice StatMech.Percolation StatMech.TwoDim

namespace MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.KestenCrossingDecay

example : Tendsto (fun n : ℕ =>
    (bernoulliProductMeasure (E := Sym2 (Site 2)) 0 zero_le_one).real
      (StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ))) atTop (𝓝 0) := by
  refine kcd_horizontal_sharpThreshold 0 zero_le_one ?_
  rw [Universality.criticalProbability_eq_pc]
  exact_mod_cast pc_pos (d := 2) (by norm_num)

example (x : Site 2) (n : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num)).real
      (kcd_localOneArm x n) = crossProb 2 (1 / 2) (by norm_num) n :=
  kcd_localOneArm_prob _ _ x n

example : crossProb 2 0 zero_le_one 1 ≤ crossProb 2 1 le_rfl 1 :=
  kcd_crossProb_mono_param zero_le_one le_rfl zero_le_one one_pos

example : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) ^ 2 * (1 * Real.exp (-1 * n))) atTop (𝓝 0) :=
  kcd_quadratic_mul_exp_tendsto_zero one_pos

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.KestenCrossingDecay
