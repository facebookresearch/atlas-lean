/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Lattice.JordanExteriorClosure
import Code.Universality.RSWStrip
import Code.Universality.RSWBxpAssembly
import Code.Universality.RSWSqrtTrick
import Code.Universality.G3PercDualityFull
import Code.RSW.Defs
import Code.Universality.Defs

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip






















theorem rbb_band_crossing_lb (a b c d : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d))
    (hmeasV : MeasurableSet (verticalCrossingEvent a b c d))
    (hsep : (horizontalCrossingEvent a b c d)ᶜ ⊆ dualVerticalCrossingEvent a b c d)
    (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent a b c d)
                = rba_selfDualMeasure.real (horizontalCrossingEvent a b c d)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent a b c d) := by
  rw [hsqsym]
  exact rst_selfDual_box_crossing_half a b c d hmeasH hmeasV hsep hsqsym

















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
























theorem rbb_rectangle_crossing_uniform
    (hpa : PositivelyAssociated rba_selfDualMeasure) {a m m' b c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d)
    (hL : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a m' c d))
    (hR : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent m b c d))
    (hmeasHB : MeasurableSet (horizontalCrossingEvent m m' c d))
    (hmeasVB : MeasurableSet (verticalCrossingEvent m m' c d))
    (hsepB : (horizontalCrossingEvent m m' c d)ᶜ ⊆ dualVerticalCrossingEvent m m' c d)
    (hsqsymB : rba_selfDualMeasure.real (verticalCrossingEvent m m' c d)
                = rba_selfDualMeasure.real (horizontalCrossingEvent m m' c d)) :
    (1 : ℝ) / 8 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
  
  have hVlb : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent m m' c d) :=
    rbb_band_crossing_lb m m' c d hmeasHB hmeasVB hsepB hsqsymB
  
  have hglue := rba_glued_rectangle_lower_bound rba_selfDualMeasure hpa
    ham hmm' hm'b hamL hmbR hcd hL hR hVlb (by norm_num)
  
  have : ((1 : ℝ) / 2) / 4 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) :=
    hglue
  linarith

end Universality

end StatMech
