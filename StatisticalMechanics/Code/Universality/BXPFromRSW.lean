/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Code.Universality.CrossingTranslationInvariance

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip













theorem bxr_twoDim_horizontalCrossingEvent_eq (a b : ℤ) :
    StatMech.TwoDim.horizontalCrossingEvent a b
      = StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b := by
  ext ω
  rw [StatMech.TwoDim.mem_horizontalCrossingEvent,
    StatMech.RSW.Box.mem_horizontalCrossingEvent,
    StatMech.RSW.Box.horizontalCrossing_eq_twoDim]



theorem bxr_twoDim_verticalCrossingEvent_eq (a b : ℤ) :
    StatMech.TwoDim.verticalCrossingEvent a b
      = StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b := rfl








theorem bxr_translatedHorizontalCrossingEvent_eq (τ : Site 2) (a b : ℤ) :
    translatedHorizontalCrossingEvent τ a b
      = translateConfig τ ⁻¹' StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b := by
  rw [translatedHorizontalCrossingEvent, bxr_twoDim_horizontalCrossingEvent_eq]



theorem bxr_translatedVerticalCrossingEvent_eq (τ : Site 2) (a b : ℤ) :
    translatedVerticalCrossingEvent τ a b
      = translateConfig τ ⁻¹' StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b := by
  rw [translatedVerticalCrossingEvent, bxr_twoDim_verticalCrossingEvent_eq]







theorem bxr_translatedHorizontalCrossing_invariant (τ : Site 2) (a b : ℤ)
    (hmeas : MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b)) :
    rba_selfDualMeasure.real (translatedHorizontalCrossingEvent τ a b)
      = rba_selfDualMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b) := by
  rw [bxr_translatedHorizontalCrossingEvent_eq,
    ← cti_horizontalCrossingEvent_translate 0 a 0 b τ]
  have h := cti_horizontalCrossing_translation_invariant 0 a 0 b τ hmeas
  simpa using h



theorem bxr_translatedVerticalCrossing_invariant (τ : Site 2) (a b : ℤ)
    (hmeas : MeasurableSet (StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b)) :
    rba_selfDualMeasure.real (translatedVerticalCrossingEvent τ a b)
      = rba_selfDualMeasure.real (StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b) := by
  rw [bxr_translatedVerticalCrossingEvent_eq,
    ← cti_verticalCrossingEvent_translate 0 a 0 b τ]
  have h := cti_verticalCrossing_translation_invariant 0 a 0 b τ hmeas
  simpa using h






theorem bxr_floor_natMul (k0 n : ℕ) :
    ⌊(k0 : ℝ) * (n : ℝ)⌋ = (k0 : ℤ) * (n : ℤ) := by
  rw [← Int.cast_natCast (n := k0), ← Int.cast_natCast (n := n), ← Int.cast_mul]
  exact Int.floor_intCast _





























theorem bxr_uniform_seed
    (hpa : PositivelyAssociated rba_selfDualMeasure)
    {k0 : ℕ} (hk0 : 2 ≤ k0) {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hmeasH : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
    (hmeasV : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)))
    (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
    (h2box : ∀ n : ℤ, 0 < n →
      γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
    (hrefl : ∀ n : ℤ, 0 < n →
      rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
    (∀ (n : ℕ) (τ : Site 2), 1 ≤ n →
        β * ((1 / 2) * γ) ^ (k0 - 1)
          ≤ rba_selfDualMeasure.real
              (translatedHorizontalCrossingEvent τ ⌊(k0 : ℝ) * (n : ℝ)⌋ (n : ℤ)))
      ∧ (∀ (n : ℕ) (τ : Site 2), 1 ≤ n →
        β * ((1 / 2) * γ) ^ (k0 - 1)
          ≤ rba_selfDualMeasure.real
              (translatedVerticalCrossingEvent τ (n : ℤ) ⌊(k0 : ℝ) * (n : ℝ)⌋)) := by
  
  
  have hk1 : 1 ≤ k0 := le_trans (by norm_num) hk0
  have hbase : ∀ n : ℤ, 0 < n →
      β * ((1 / 2) * γ) ^ (k0 - 1) ≤ rai_cross rba_selfDualMeasure n k0 := by
    intro n hn
    exact rai_cross_lb rba_selfDualMeasure hpa hn hβ hγ (hseed n hn)
      (cti_h2box_discharge (hmeas2box n hn) (h2box n hn))
      (cti_hband_discharge (hmeasband n hn) (hband n hn)) k0 hk1
  refine ⟨?_, ?_⟩
  · 
    intro n τ hn1
    have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    rw [bxr_floor_natMul,
      bxr_translatedHorizontalCrossing_invariant τ ((k0 : ℤ) * (n : ℤ)) (n : ℤ)
        (hmeasH (n : ℤ) hn)]
    have := hbase (n : ℤ) hn
    rwa [rai_cross_def] at this
  · 
    intro n τ hn1
    have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    rw [bxr_floor_natMul,
      bxr_translatedVerticalCrossing_invariant τ (n : ℤ) ((k0 : ℤ) * (n : ℤ))
        (hmeasV (n : ℤ) hn), hrefl (n : ℤ) hn]
    have := hbase (n : ℤ) hn
    rwa [rai_cross_def] at this




















theorem bxr_boxCrossingProperty
    (hpa : PositivelyAssociated rba_selfDualMeasure)
    {k0 : ℕ} (hk0 : 2 ≤ k0) {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hmeasH : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
    (hmeasV : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)))
    (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
    (h2box : ∀ n : ℤ, 0 < n →
      γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
    (hrefl : ∀ n : ℤ, 0 < n →
      rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
    BoxCrossingProperty rba_selfDualMeasure (k0 : ℝ) := by
  obtain ⟨hHseed, hVseed⟩ :=
    bxr_uniform_seed hpa hk0 hβ hγ hmeas2box hmeasband hmeasH hmeasV hseed h2box hband hrefl
  have hρ : (1 : ℝ) < (k0 : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hk0
  have hc : (0 : ℝ) < β * ((1 / 2) * γ) ^ (k0 - 1) := by positivity
  exact rba_bxp_of_uniform_seed rba_selfDualMeasure (k0 : ℝ) hρ 1
    (β * ((1 / 2) * γ) ^ (k0 - 1)) hc
    (fun n τ hn => hHseed n τ hn) (fun n τ hn => hVseed n τ hn)

end Universality

end StatMech
