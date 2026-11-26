/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangFaithfulExclusive

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangFaithfulExclusive`

* `zfe_percolationProbability_zero`: `θ(1/2) = 0` (unconditional);
* `zfe_criticalProbability_eq_half`: `p_c(ℤ²) = 1/2` (unconditional);
* `zfe_faithfulMatchedExclusive` at `N = 3`;
* `zfe_primalEmb` and `zfe_faceEmb` at the site `(1, 2)`: `(2, 4)` and `(3, 5)`, distinct.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangFaithfulExclusive

open _root_.StatMech _root_.StatMech.TwoDim _root_.StatMech.Lattice _root_.StatMech.Universality
open _root_.StatMech.Percolation _root_.StatMech.RSW.Box

-- No percolation at `p = 1/2`.
example : percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0 :=
  zfe_percolationProbability_zero

-- Kesten's theorem.
example : criticalProbability 2 = (1 : ℝ) / 2 := zfe_criticalProbability_eq_half

-- Primal horizontal and face-dual vertical crossings are exclusive at `N = 3`.
example := zfe_faithfulMatchedExclusive 3

-- The doubled-lattice embeddings of `(1, 2)`.
example : zfe_primalEmb ![1, 2] = ![2, 4] ∧ zfe_faceEmb ![1, 2] = ![3, 5] ∧
    zfe_primalEmb ![1, 2] ≠ zfe_faceEmb ![1, 2] := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · intro h
    have := congrFun h 0
    simp [zfe_primalEmb, zfe_faceEmb] at this

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangFaithfulExclusive
