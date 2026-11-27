/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.CriticalReduction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.CriticalReduction`

At `q = 4` the triangular critical odds are `y = 1`, i.e. `p = 1/2`, and
`dualParam (1/2) 4 = 4/5` (hexagonal odds `4`):
* `TriangularCriticalPhaseBoundary 4 (1/2)` holds (non-vacuity: the cubic
  `y³ + 3y² - 4 = (y - 1)(y + 2)²` changes sign exactly at `p = 1/2`);
* `triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase` applied to it yields both
  critical polynomials at `p = 1/2`, `p = 4/5`;
* `wiredTwoPointProbability` vanishes outside `p ∈ (0, 1)` (at `p = 0`);
* `TriHexSubcriticalDecayTransfer` holds when the hexagonal threshold is `0` (vacuous decay).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.CriticalReduction

open Set _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.FK.TriHex
open _root_.StatMech.BeffaraDC

/-- The triangular cubic at `q = 4` changes sign exactly at `p = 1/2`. -/
theorem tri_phase_four : TriangularCriticalPhaseBoundary 4 (1 / 2) := by
  intro p hp
  obtain ⟨hp0, hp1⟩ := hp
  have h1 : 0 < 1 - p := by linarith
  have hfac : triangularFKCriticalPolynomial 4 (fkEdgeOdds p) =
      (fkEdgeOdds p - 1) * (fkEdgeOdds p + 2) ^ 2 := by
    unfold triangularFKCriticalPolynomial
    ring
  have hy : 0 < fkEdgeOdds p := div_pos hp0 h1
  have hsq : 0 < (fkEdgeOdds p + 2) ^ 2 := by positivity
  have hlt : fkEdgeOdds p < 1 ↔ p < 1 / 2 := by
    unfold fkEdgeOdds
    rw [div_lt_one h1]
    constructor <;> intro h <;> linarith
  have hgt : 1 < fkEdgeOdds p ↔ 1 / 2 < p := by
    unfold fkEdgeOdds
    rw [one_lt_div h1]
    constructor <;> intro h <;> linarith
  dsimp only
  rw [hfac, ← hlt, ← hgt]
  refine ⟨⟨fun h => ?_, fun h => mul_neg_of_neg_of_pos (by linarith) hsq⟩,
    ⟨fun h => ?_, fun h => mul_pos (by linarith) hsq⟩⟩
  · by_contra hc
    have := mul_nonneg (by linarith : 0 ≤ fkEdgeOdds p - 1) hsq.le
    linarith
  · by_contra hc
    have := mul_nonpos_of_nonpos_of_nonneg (by linarith : fkEdgeOdds p - 1 ≤ 0) hsq.le
    linarith

-- Both critical polynomials at the dual pair `(1/2, 4/5)` from the triangular phase input.
example : triangularFKCriticalPolynomial 4 (fkEdgeOdds (1 / 2)) = 0 ∧
    hexagonalFKCriticalPolynomial 4 (fkEdgeOdds (4 / 5)) = 0 :=
  triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase (by norm_num)
    ⟨by norm_num, by norm_num⟩ (by norm_num [dualParam]) tri_phase_four

-- The two-point probability is `0` outside the admissible parameter range.
example (x y : _root_.StatMech.Lattice.Site 2) :
    triangular.wiredTwoPointProbability 0 4 x y = 0 := by
  simp [PeriodicGraph.wiredTwoPointProbability]

-- With hexagonal threshold `0` the decay transfer is vacuous.
example : TriHexSubcriticalDecayTransfer 4 (1 / 2) 0 := by
  intro _ p hp
  exact absurd hp.2 (not_lt.2 hp.1.le)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.CriticalReduction
