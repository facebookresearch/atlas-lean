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

Corollaries of the self-duality bound `rst_selfDual_box_crossing_half` and of gluing: a vertical
crossing bound `1/2` for a band, the square-root trick stated for vertical crossings, and the bound
`1/8` for a rectangle glued from two horizontal crossings of probability `≥ 1/2` and a band.

All `ℙ_{1/2}` statements here assume the separation hypothesis `hsep` of
`rst_selfDual_box_crossing_half`, which is not planar duality and fails for `[0, 2]²`.

## Main results

* `StatMech.Universality.rbb_band_crossing_lb`.
* `StatMech.Universality.rbb_band_crossing_sqrt_lb`.
* `StatMech.Universality.rbb_rectangle_crossing_uniform`.
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-- `ℙ_{1/2}(V[a, b] × [c, d]) ≥ 1/2` under the hypotheses of `rst_selfDual_box_crossing_half`
(including `hsep`, which fails for `[0, 2]²`). -/
theorem rbb_band_crossing_lb (a b c d : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d))
    (hmeasV : MeasurableSet (verticalCrossingEvent a b c d))
    (hsep : (horizontalCrossingEvent a b c d)ᶜ ⊆ dualVerticalCrossingEvent a b c d)
    (hsqsym : halfMeasure.real (verticalCrossingEvent a b c d)
                = halfMeasure.real (horizontalCrossingEvent a b c d)) :
    (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent a b c d) := by
  rw [hsqsym]
  exact rst_selfDual_box_crossing_half a b c d hmeasH hmeasV hsep hsqsym

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

/-- If the two overlapping horizontal crossings have `ℙ_{1/2}`-probability at least `1/2` and the
overlap satisfies the hypotheses of `rbb_band_crossing_lb`, the glued rectangle is crossed with
probability at least `1/8`. Inherits `hsepB`, which fails for `[0, 2]²`. -/
theorem rbb_rectangle_crossing_uniform
    (hpa : PositivelyAssociated halfMeasure) {a m m' b c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d)
    (hL : (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent a m' c d))
    (hR : (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent m b c d))
    (hmeasHB : MeasurableSet (horizontalCrossingEvent m m' c d))
    (hmeasVB : MeasurableSet (verticalCrossingEvent m m' c d))
    (hsepB : (horizontalCrossingEvent m m' c d)ᶜ ⊆ dualVerticalCrossingEvent m m' c d)
    (hsqsymB : halfMeasure.real (verticalCrossingEvent m m' c d)
                = halfMeasure.real (horizontalCrossingEvent m m' c d)) :
    (1 : ℝ) / 8 ≤ halfMeasure.real (horizontalCrossingEvent a b c d) := by
  have hVlb : (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent m m' c d) :=
    rbb_band_crossing_lb m m' c d hmeasHB hmeasVB hsepB hsqsymB
  have hglue := rba_glued_rectangle_lower_bound halfMeasure hpa
    ham hmm' hm'b hamL hmbR hcd hL hR hVlb (by norm_num)
  have : ((1 : ℝ) / 2) / 4 ≤ halfMeasure.real (horizontalCrossingEvent a b c d) :=
    hglue
  linarith

end Universality

end StatMech
