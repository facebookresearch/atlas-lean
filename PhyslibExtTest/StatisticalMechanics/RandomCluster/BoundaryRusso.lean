/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryRusso

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryRusso`

On the one-edge graph `⊤` on `Fin 2` with empty wiring `⊥`, at `p = 1/2`, `q = 2`:
* `bcMean_const`: the expectation of a constant is the constant (the partition function is
  positive);
* `hasDerivAt_bcMean` for the constant function `1`;
* `hasDerivAt_bcProbOf` (Russo's formula in `p`) for the sure event.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BoundaryRusso

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

/-- The boundary-conditioned partition function at `p = 1/2`, `q = 2` is nonzero. -/
theorem bcZ_ne : bcZ G2 ⊥ (1 / 2) 2 ≠ 0 :=
  (bcZ_pos G2 ⊥ (by norm_num) (by norm_num) (by norm_num)).ne'

-- The expectation of a constant.
example : bcMean G2 ⊥ (1 / 2) 2 (fun _ => 7) = 7 := bcMean_const G2 ⊥ _ _ bcZ_ne

-- The `p`-derivative of an expectation.
example : HasDerivAt (fun p => bcMean G2 ⊥ p 2 (fun _ => 1))
    ((∑ e ∈ G2.edgeFinset, bcCov G2 ⊥ (1 / 2) 2 (fun _ => 1) (coord e)) /
      (1 / 2 * (1 - 1 / 2))) (1 / 2) :=
  hasDerivAt_bcMean G2 ⊥ (by norm_num) (by norm_num) (by norm_num) _

-- Russo's formula for the sure event.
example : HasDerivAt (fun p => bcProbOf G2 ⊥ p 2 Set.univ)
    ((∑ e ∈ G2.edgeFinset, bcCov G2 ⊥ (1 / 2) 2 (Set.univ.indicator fun _ => (1 : ℝ))
      (coord e)) / (1 / 2 * (1 - 1 / 2))) (1 / 2) :=
  hasDerivAt_bcProbOf G2 ⊥ (by norm_num) (by norm_num) (by norm_num) _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BoundaryRusso
