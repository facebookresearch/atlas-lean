/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Code.Universality.BXPAllAspect
import Code.Universality.ConnectedRCoastClose
import Code.Universality.CrossingReflection
import Code.Universality.RSWBandBound

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip















theorem bmh_square_reflection (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n)) :
    rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n)
      = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) :=
  crf_verticalCrossing_eq_horizontal_swap 0 n 0 n hmeasH
















theorem bmh_square_seed_half (n : ℤ) (_hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) :
    (1 : ℝ) / 2 ≤ rai_cross rba_selfDualMeasure n 1 := by
  rw [rai_cross_def]
  have h1n : ((1 : ℕ) : ℤ) * n = n := by push_cast; ring
  rw [h1n]
  exact rst_square_crossing_half n hmeasH hmeasV hsep (bmh_square_reflection n hmeasH)














theorem bmh_band_seed_half (n : ℤ) (_hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) :=
  rbb_band_crossing_lb 0 n 0 n hmeasH hmeasV hsep (bmh_square_reflection n hmeasH)


theorem bmh_square_seed_half_faithful (n : ℤ) (hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    (1 : ℝ) / 2 ≤ rai_cross rba_selfDualMeasure n 1 := by
  rw [rai_cross_def]
  have h1n : ((1 : ℕ) : ℤ) * n = n := by push_cast; ring
  rw [h1n]
  exact crr_square_half n hn hmeasH hmeasFace hmeasThin



theorem bmh_band_seed_half_faithful (n : ℤ) (hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) := by
  rw [bmh_square_reflection n hmeasH]
  exact crr_square_half n hn hmeasH hmeasFace hmeasThin














































theorem bmh_boxCrossingProperty_selfDual
    (hpa : PositivelyAssociated rba_selfDualMeasure)
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hsepSquare : ∀ n : ℤ, 0 < n →
      (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
    (h2box : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 8 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n)) :
    ∀ ρ : ℝ, 1 < ρ → BoxCrossingProperty rba_selfDualMeasure ρ := by
  apply bxa_boxCrossingProperty_all hpa (β := 1 / 2) (γ := 1 / 8)
    (by norm_num) (by norm_num)
  · 
    intro n hn
    exact hmeasGenH (2 * n) n (by omega) hn
  · 
    intro n hn
    exact hmeasGenV n n hn hn
  · exact hmeasGenH
  · exact hmeasGenV
  · 
    intro n hn
    exact bmh_square_seed_half n hn (hmeasGenH n n hn hn) (hmeasGenV n n hn hn)
      (hsepSquare n hn)
  · 
    exact h2box
  · 
    intro n hn
    exact bmh_band_seed_half n hn (hmeasGenH n n hn hn) (hmeasGenV n n hn hn)
      (hsepSquare n hn)
  · 
    exact crf_hrefl (fun k0 hk0 n hn =>
      hmeasGenH ((k0 : ℤ) * n) n (by positivity) hn)



theorem bmh_boxCrossingProperty_selfDual_faithful
    (hpa : PositivelyAssociated rba_selfDualMeasure)
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1)))
    (h2box : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 8 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n)) :
    ∀ ρ : ℝ, 1 < ρ → BoxCrossingProperty rba_selfDualMeasure ρ := by
  apply bxa_boxCrossingProperty_all hpa (β := 1 / 2) (γ := 1 / 8)
    (by norm_num) (by norm_num)
  · intro n hn
    exact hmeasGenH (2 * n) n (by omega) hn
  · intro n hn
    exact hmeasGenV n n hn hn
  · exact hmeasGenH
  · exact hmeasGenV
  · intro n hn
    exact bmh_square_seed_half_faithful n hn (hmeasGenH n n hn hn)
      (hmeasFace n hn) (hmeasThin n hn)
  · exact h2box
  · intro n hn
    exact bmh_band_seed_half_faithful n hn (hmeasGenH n n hn hn)
      (hmeasFace n hn) (hmeasThin n hn)
  · exact crf_hrefl (fun k0 hk0 n hn =>
      hmeasGenH ((k0 : ℤ) * n) n (by positivity) hn)

end Universality

end StatMech
