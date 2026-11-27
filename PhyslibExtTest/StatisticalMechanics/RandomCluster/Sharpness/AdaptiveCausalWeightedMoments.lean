/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalWeightedMoments

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalWeightedMoments`

Both checks use the random-cluster mass on the complete graph on `Fin 2` at `p = 1/2`, `q = 2`,
and the one-query decision tree on `s(0, 1)`.

* `sum_coord_mul_flipCrossTripleProb_right_extendDecisionTreeTriple` at phase `0`, edge `s(0, 1)`;
* `flipCrossTripleProb_structured_orientations`, both orientations.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalWeightedMoments

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCausalKernel
open _root_.StatMech.OSSS.MonotonicFK

/-- The random-cluster mass on `K₂` at `p = 1/2`, `q = 2`. -/
local notation "μ₂" => fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2

/-- Positivity of `μ₂`. -/
theorem mu2_pos (ω : ConfigSpace (Sym2 (Fin 2))) : 0 < μ₂ ω :=
  fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num) ω

/-- `μ₂` is a probability mass. -/
theorem mu2_sum : ∑ ω, μ₂ ω = 1 :=
  fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)

-- Weighted right marginal of the flipped cross coupling on `K₂`.
example (driver left rightSeed known : ConfigSpace (Sym2 (Fin 2))) :
    (∑ right, Lindeberg.coord s(0, 1) right *
      flipCrossTripleProb μ₂ ∅ driver left right s(0, 1)
        (extendDecisionTreeTriple (some 0) (.node s(0, 1) (.leaf true) (.leaf false)) known
          Finset.univ)) =
      Lindeberg.mean μ₂ (Lindeberg.coord s(0, 1)) * μ₂ left *
        flipBaseProb μ₂ ∅ driver s(0, 1)
          (extendDecisionTreeTriple (some 0) (.node s(0, 1) (.leaf true) (.leaf false)) known
            Finset.univ) :=
  sum_coord_mul_flipCrossTripleProb_right_extendDecisionTreeTriple _ mu2_pos
    mu2_sum driver left rightSeed s(0, 1) 0 _ known

-- Both orientations of the structured identity, for the one-query tree on `K₂`.
example (seed : ConfigSpace (Sym2 (Fin 2))) (t : ℕ) :=
  flipCrossTripleProb_structured_orientations μ₂ mu2_pos
    mu2_sum (.node s(0, 1) (.leaf true) (.leaf false)) seed t s(0, 1)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalWeightedMoments
