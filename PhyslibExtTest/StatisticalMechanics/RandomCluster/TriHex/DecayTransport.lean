/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.DecayTransport

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.DecayTransport`

* `SubcriticalTwoPointComparison` is satisfiable: the triangular lattice compares with itself
  through the identity map (`K = a = 1`, `b = 0`);
* `subcriticalTwoPointExponentialDecay_of_comparison` applied to that self-comparison;
* `TriHexGlobalProbabilityComparison 0 (1/2) (1/2)` holds non-vacuously (at `q = 0` both
  two-point functions vanish), and `triHexGlobalTwoPointComparison_of_probabilityComparison`
  turns it into the distance-and-probability comparison;
* `triHexSubcriticalDecayTransfer_of_probabilityComparison` on the same instance.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.DecayTransport

open Set _root_.StatMech.FK.PeriodicPlanar

/-- The triangular lattice compares with itself through the identity map. -/
theorem tri_self_comparison (q pc : ℝ) :
    SubcriticalTwoPointComparison triangular triangular q pc pc := by
  intro p hp
  refine ⟨p, hp, 1, 1, 0, one_pos, one_pos, le_rfl, id, fun x y => ?_, fun x y => ?_⟩
  · simp
  · simp

-- Decay transfers along the self-comparison.
example (q pc : ℝ) (h : SubcriticalTwoPointExponentialDecay triangular q pc) :
    SubcriticalTwoPointExponentialDecay triangular q pc :=
  subcriticalTwoPointExponentialDecay_of_comparison (tri_self_comparison q pc) h

/-- At `q = 0` the probability comparison holds with `pTri = p`, `K = 1`. -/
theorem prob_comparison_zero : TriHexGlobalProbabilityComparison 0 (1 / 2) (1 / 2) := by
  intro p hp
  refine ⟨p, hp, 1, one_pos, fun u v => ?_⟩
  simp [PeriodicGraph.wiredTwoPointProbability]

-- The probability comparison yields the global two-point comparison.
example : TriHexGlobalTwoPointComparison 0 (1 / 2) (1 / 2) :=
  triHexGlobalTwoPointComparison_of_probabilityComparison prob_comparison_zero

-- ... and the triangular-to-hexagonal decay transfer.
example : TriHexSubcriticalDecayTransfer 0 (1 / 2) (1 / 2) :=
  triHexSubcriticalDecayTransfer_of_probabilityComparison prob_comparison_zero

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.DecayTransport
