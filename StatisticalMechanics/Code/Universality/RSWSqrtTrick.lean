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












theorem rst_selfDual_box_crossing_half (a b c d : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d))
    (hmeasV : MeasurableSet (verticalCrossingEvent a b c d))
    (hsep : (horizontalCrossingEvent a b c d)ᶜ ⊆ dualVerticalCrossingEvent a b c d)
    (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent a b c d)
                = rba_selfDualMeasure.real (horizontalCrossingEvent a b c d)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
  have hselfDual : rba_selfDualMeasure.real (dualVerticalCrossingEvent a b c d)
      = rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
    rw [rba_dualVerticalCrossing_eq a b c d hmeasV, hsqsym]
  have hcompl : rba_selfDualMeasure.real (horizontalCrossingEvent a b c d)ᶜ
      = 1 - rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
    rw [measureReal_compl hmeasH, probReal_univ]
  have hmono : rba_selfDualMeasure.real (horizontalCrossingEvent a b c d)ᶜ
      ≤ rba_selfDualMeasure.real (dualVerticalCrossingEvent a b c d) :=
    measureReal_mono hsep
  rw [hselfDual, hcompl] at hmono
  linarith















theorem rst_square_crossing_half (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
    (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n)
                = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) :=
  rba_self_dual_square_half n hmeasH hmeasV hsep hsqsym




theorem rst_square_vertical_crossing_half (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
    (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n)
                = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) := by
  rw [hsqsym]
  exact rst_square_crossing_half n hmeasH hmeasV hsep hsqsym




















theorem rst_rectangle_crossing_pos
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {n : ℤ} {v0 : ℝ} (hn : 0 < n)
    (hL : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent 0 n 0 n))
    (hR : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent n (2 * n) 0 n))
    (hVlb : v0 ≤ μ.real (verticalCrossingEvent n n 0 n)) (hv0 : 0 ≤ v0) :
    v0 / 4 ≤ μ.real (horizontalCrossingEvent 0 (2 * n) 0 n) :=
  rba_glued_rectangle_lower_bound μ hpa
    (a := 0) (m := n) (m' := n) (b := 2 * n) (c := 0) (d := n)
    (le_of_lt hn) (le_refl n) (by linarith) hn (by linarith) (le_of_lt hn)
    hL hR hVlb hv0









theorem rst_selfDual_rectangle_crossing_pos
    (hpa : PositivelyAssociated rba_selfDualMeasure) {n : ℤ} {v0 : ℝ} (hn : 0 < n)
    (hmeasHL : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasVL : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsepL : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
    (hsqsymL : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n)
                = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n))
    (hmeasHR : MeasurableSet (horizontalCrossingEvent n (2 * n) 0 n))
    (hmeasVR : MeasurableSet (verticalCrossingEvent n (2 * n) 0 n))
    (hsepR : (horizontalCrossingEvent n (2 * n) 0 n)ᶜ
                ⊆ dualVerticalCrossingEvent n (2 * n) 0 n)
    (hsqsymR : rba_selfDualMeasure.real (verticalCrossingEvent n (2 * n) 0 n)
                = rba_selfDualMeasure.real (horizontalCrossingEvent n (2 * n) 0 n))
    (hVlb : v0 ≤ rba_selfDualMeasure.real (verticalCrossingEvent n n 0 n)) (hv0 : 0 ≤ v0) :
    v0 / 4 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n) := by
  have hL : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) :=
    rst_square_crossing_half n hmeasHL hmeasVL hsepL hsqsymL
  
  have hR : (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent n (2 * n) 0 n) :=
    rst_selfDual_box_crossing_half n (2 * n) 0 n hmeasHR hmeasVR hsepR hsqsymR
  exact rst_rectangle_crossing_pos rba_selfDualMeasure hpa hn hL hR hVlb hv0

end Universality

end StatMech
