/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BoxVanHoveLimit

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.fkc_rqvanhove`

* `fsc_logistic 0 = 1/2`, so logit parameter `s = 0` is edge density `p = 1/2`;
* `fkc_u_q2`: at `q = 2` the box free energy is the `EdgeConfigZ` one;
* `fkc_f` is `fkc_u` divided by the number of box edges;
* the headline `fkc_perEdgeDensityConverges` at `d = 2`, `s = 0`, `q = 2` (FK–Ising) and at
  `d = 1`, `q = 1` (Bernoulli percolation), unfolded to a convergent sequence.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.fkc_rqvanhove

open Filter Topology _root_.StatMech _root_.StatMech.Walls _root_.StatMech.FK

-- Logit `0` is edge density `1/2`.
example : fsc_logistic 0 = 1 / 2 := by
  rw [fsc_logistic, Real.exp_zero]; norm_num

-- At `q = 2` the box free energy is the `EdgeConfigZ` box free energy.
example (d n : ℕ) (s : ℝ) : fkc_u d s 2 n = ecz_u d s n := fkc_u_q2 d s n

-- The per-edge free energy divides by the number of box edges.
example (d n : ℕ) (s q : ℝ) :
    fkc_f d s q n = fkc_u d s q n / ((boxGraph d n).edgeFinset.card : ℝ) := rfl

-- The van Hove limit for the FK–Ising model on `ℤ²` at `p = 1/2`: the per-edge free energy of
-- the box `[-n, n]²` converges.
example : ∃ ρ : ℝ, Tendsto (fun n => fkc_f 2 0 2 n) atTop (𝓝 ρ) :=
  fkc_perEdgeDensityConverges 2 (by norm_num) 0 2 (by norm_num)

-- The van Hove limit for Bernoulli percolation (`q = 1`) on `ℤ` at logit `s = 1`.
example : fkc_PerEdgeDensityConverges 1 1 1 :=
  fkc_perEdgeDensityConverges 1 (le_refl 1) 1 1 (le_refl 1)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.fkc_rqvanhove
