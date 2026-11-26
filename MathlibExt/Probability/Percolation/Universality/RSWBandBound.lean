/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.RSWSqrtTrick

/-!
# Band and rectangle crossing bounds at `p = 1/2`

The square-root trick stated for vertical crossings, for a positively associated measure.

The band bound `rbb_band_crossing_lb` and the glued-rectangle bound
`rbb_rectangle_crossing_uniform` were removed: they depended on the self-duality bound
`rst_selfDual_box_crossing_half`, whose separation hypothesis `hsep` is not planar duality and
fails for `[0, 2]²`, so they had no nondegenerate instance.

## Main results

* `StatMech.Universality.rbb_band_crossing_sqrt_lb`.
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-- Square-root trick for the vertical crossing: `μ(V) ≥ 1 - √(1 - s)` when `μ(H ∪ V) ≥ s` and
`μ(V) = μ(H)`. -/
theorem rbb_band_crossing_sqrt_lb
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a b c d : ℤ} {s : ℝ}
    (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d))
    (hmeasV : MeasurableSet (verticalCrossingEvent a b c d))
    (hsym : μ.real (verticalCrossingEvent a b c d)
              = μ.real (horizontalCrossingEvent a b c d))
    (hunion : s ≤ μ.real (horizontalCrossingEvent a b c d ∪ verticalCrossingEvent a b c d)) :
    1 - Real.sqrt (1 - s) ≤ μ.real (verticalCrossingEvent a b c d) := by
  rw [hsym]
  exact rba_sqrt_square_seed μ hpa hmeasH hmeasV hsym hunion

end Universality

end StatMech
