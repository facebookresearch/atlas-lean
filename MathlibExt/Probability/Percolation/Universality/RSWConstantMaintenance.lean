/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.RSWBandBound

/-!
# One gluing step with a band of probability `1/2`

For a positively associated measure, gluing a horizontal crossing with constant `cL`, a band
crossed vertically with probability at least `1/2`, and a horizontal crossing with constant `cR`
gives the constant `cL · (1/2) · cR` for the longer rectangle. This is the induction step that
keeps crossing constants positive when the aspect ratio grows.

## Main results

* `StatMech.Universality.rcm_aspect_step`, `StatMech.Universality.rcm_aspect_step_pos`.
* `StatMech.Universality.rcm_aspect_step_selfDual`: the `ℙ_{1/2}` version, with the band bound from
  `rbb_band_crossing_lb` (and hence its separation hypothesis, which fails for `[0, 2]²`).
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-- Gluing step: `cL · (1/2) · cR ≤ μ(H[a, b] × [c, d])` from bounds on the two overlapping
horizontal crossings and the bound `1/2` on the vertical crossing of the overlap. -/
theorem rcm_aspect_step
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ} {cL cR : ℝ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d)
    (hcL0 : 0 ≤ cL) (hcR0 : 0 ≤ cR)
    (hL : cL ≤ μ.real (horizontalCrossingEvent a m' c d))
    (hR : cR ≤ μ.real (horizontalCrossingEvent m b c d))
    (hVlb : (1 : ℝ) / 2 ≤ μ.real (verticalCrossingEvent m m' c d)) :
    cL * (1 / 2) * cR ≤ μ.real (horizontalCrossingEvent a b c d) := by
  have hglue := jec_rsw_strip_glue μ hpa ham hmm' hm'b hamL hmbR hcd
  have hPHL0 : (0 : ℝ) ≤ μ.real (horizontalCrossingEvent a m' c d) := le_trans hcL0 hL
  have hPV0 : (0 : ℝ) ≤ μ.real (verticalCrossingEvent m m' c d) :=
    le_trans (by norm_num) hVlb
  have h1 : cL * (1 / 2)
      ≤ μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d) :=
    mul_le_mul hL hVlb (by norm_num) hPHL0
  have h2 : cL * (1 / 2) * cR
      ≤ μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d)
          * μ.real (horizontalCrossingEvent m b c d) :=
    mul_le_mul h1 hR hcR0 (mul_nonneg hPHL0 hPV0)
  exact le_trans h2 hglue

/-- Positivity form of `rcm_aspect_step`. -/
theorem rcm_aspect_step_pos
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ} {cL cR : ℝ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (hL : cL ≤ μ.real (horizontalCrossingEvent a m' c d))
    (hR : cR ≤ μ.real (horizontalCrossingEvent m b c d))
    (hVlb : (1 : ℝ) / 2 ≤ μ.real (verticalCrossingEvent m m' c d)) :
    0 < μ.real (horizontalCrossingEvent a b c d) := by
  have hstep := rcm_aspect_step μ hpa ham hmm' hm'b hamL hmbR hcd
    (le_of_lt hcL) (le_of_lt hcR) hL hR hVlb
  have hpos : 0 < cL * (1 / 2) * cR := by positivity
  exact lt_of_lt_of_le hpos hstep

/-- `rcm_aspect_step` for `ℙ_{1/2}`, with the band bound supplied by `rbb_band_crossing_lb`; this
inherits its separation hypothesis `hsepB`, which fails for `[0, 2]²`. -/
theorem rcm_aspect_step_selfDual
    (hpa : PositivelyAssociated halfMeasure) {a m m' b c d : ℤ} {cL cR : ℝ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d)
    (hcL0 : 0 ≤ cL) (hcR0 : 0 ≤ cR)
    (hL : cL ≤ halfMeasure.real (horizontalCrossingEvent a m' c d))
    (hR : cR ≤ halfMeasure.real (horizontalCrossingEvent m b c d))
    (hmeasHB : MeasurableSet (horizontalCrossingEvent m m' c d))
    (hmeasVB : MeasurableSet (verticalCrossingEvent m m' c d))
    (hsepB : (horizontalCrossingEvent m m' c d)ᶜ ⊆ dualVerticalCrossingEvent m m' c d)
    (hsqsymB : halfMeasure.real (verticalCrossingEvent m m' c d)
                = halfMeasure.real (horizontalCrossingEvent m m' c d)) :
    cL * (1 / 2) * cR ≤ halfMeasure.real (horizontalCrossingEvent a b c d) :=
  rcm_aspect_step halfMeasure hpa ham hmm' hm'b hamL hmbR hcd hcL0 hcR0 hL hR
    (rbb_band_crossing_lb m m' c d hmeasHB hmeasVB hsepB hsqsymB)

end Universality

end StatMech
