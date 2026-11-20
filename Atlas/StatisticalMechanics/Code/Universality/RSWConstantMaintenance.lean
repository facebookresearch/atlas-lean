/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































import Code.Universality.RSWBandBound

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip










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






theorem rcm_aspect_step_selfDual
    (hpa : PositivelyAssociated rba_selfDualMeasure) {a m m' b c d : ℤ} {cL cR : ℝ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d)
    (hcL0 : 0 ≤ cL) (hcR0 : 0 ≤ cR)
    (hL : cL ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a m' c d))
    (hR : cR ≤ rba_selfDualMeasure.real (horizontalCrossingEvent m b c d))
    (hmeasHB : MeasurableSet (horizontalCrossingEvent m m' c d))
    (hmeasVB : MeasurableSet (verticalCrossingEvent m m' c d))
    (hsepB : (horizontalCrossingEvent m m' c d)ᶜ ⊆ dualVerticalCrossingEvent m m' c d)
    (hsqsymB : rba_selfDualMeasure.real (verticalCrossingEvent m m' c d)
                = rba_selfDualMeasure.real (horizontalCrossingEvent m m' c d)) :
    cL * (1 / 2) * cR ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) :=
  rcm_aspect_step rba_selfDualMeasure hpa ham hmm' hm'b hamL hmbR hcd hcL0 hcR0 hL hR
    (rbb_band_crossing_lb m m' c d hmeasHB hmeasVB hsepB hsqsymB)

end Universality

end StatMech
