/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.CrossingTranslationInvariance

/-!
# The box-crossing property at `p = 1/2` from RSW crossing bounds, integer aspect ratios

For an integer aspect ratio `k₀ ≥ 2`, the aspect-ratio induction `rai_cross_lb`, translation
invariance and the diagonal reflection turn bounds on crossings of rectangles at the origin into
the box-crossing property `BoxCrossingProperty ℙ_{1/2} k₀`.

The inputs of `bxr_boxCrossingProperty` are: positive association of `ℙ_{1/2}` (`hpa`, the
Harris–FKG inequality for all increasing sets; not proved in Atlas for the infinite product
measure), a square crossing bound `β` (`hseed`), a bound `γ` on the crossings of `[0, 2n] × [0, n]`
for all `n` (`h2box`; this is the Russo–Seymour–Welsh theorem), the band bound `1/2` (`hband`),
measurability (provable: `measurableSet_horizontalCrossingEvent`) and the reflection identity
(provable: `crf_hrefl_fixed`).

## Main results

* `StatMech.Universality.bxr_translatedHorizontalCrossing_invariant`,
  `StatMech.Universality.bxr_translatedVerticalCrossing_invariant`.
* `StatMech.Universality.bxr_uniform_seed`, `StatMech.Universality.bxr_boxCrossingProperty`.

## References

* L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978), 39–48.
* P. D. Seymour, D. J. A. Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete
  Math. 3 (1978), 227–245.
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-- The `TwoDim` left–right crossing event of `[0, a] × [0, b]` is the `RSW.Box` one. -/
theorem bxr_twoDim_horizontalCrossingEvent_eq (a b : ℤ) :
    StatMech.TwoDim.horizontalCrossingEvent a b
      = StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b := by
  ext ω
  rw [StatMech.TwoDim.mem_horizontalCrossingEvent,
    StatMech.RSW.Box.mem_horizontalCrossingEvent,
    StatMech.RSW.Box.horizontalCrossing_eq_twoDim]

/-- The `TwoDim` bottom–top crossing event of `[0, a] × [0, b]` is the `RSW.Box` one. -/
theorem bxr_twoDim_verticalCrossingEvent_eq (a b : ℤ) :
    StatMech.TwoDim.verticalCrossingEvent a b
      = StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b := rfl

/-- The translated left–right crossing event as a preimage of an `RSW.Box` crossing event. -/
theorem bxr_translatedHorizontalCrossingEvent_eq (τ : Site 2) (a b : ℤ) :
    translatedHorizontalCrossingEvent τ a b
      = translateConfig τ ⁻¹' StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b := by
  rw [translatedHorizontalCrossingEvent, bxr_twoDim_horizontalCrossingEvent_eq]

/-- The translated bottom–top crossing event as a preimage of an `RSW.Box` crossing event. -/
theorem bxr_translatedVerticalCrossingEvent_eq (τ : Site 2) (a b : ℤ) :
    translatedVerticalCrossingEvent τ a b
      = translateConfig τ ⁻¹' StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b := by
  rw [translatedVerticalCrossingEvent, bxr_twoDim_verticalCrossingEvent_eq]

/-- Translated left–right crossings have the `ℙ_{1/2}`-probability of the crossing at the origin. -/
theorem bxr_translatedHorizontalCrossing_invariant (τ : Site 2) (a b : ℤ)
    (hmeas : MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b)) :
    halfMeasure.real (translatedHorizontalCrossingEvent τ a b)
      = halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b) := by
  rw [bxr_translatedHorizontalCrossingEvent_eq,
    ← cti_horizontalCrossingEvent_translate 0 a 0 b τ]
  have h := cti_horizontalCrossing_translation_invariant 0 a 0 b τ hmeas
  simpa using h

/-- Translated bottom–top crossings have the `ℙ_{1/2}`-probability of the crossing at the origin. -/
theorem bxr_translatedVerticalCrossing_invariant (τ : Site 2) (a b : ℤ)
    (hmeas : MeasurableSet (StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b)) :
    halfMeasure.real (translatedVerticalCrossingEvent τ a b)
      = halfMeasure.real (StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b) := by
  rw [bxr_translatedVerticalCrossingEvent_eq,
    ← cti_verticalCrossingEvent_translate 0 a 0 b τ]
  have h := cti_verticalCrossing_translation_invariant 0 a 0 b τ hmeas
  simpa using h

/-- `⌊k₀ n⌋ = k₀ n` for natural numbers. -/
theorem bxr_floor_natMul (k0 n : ℕ) :
    ⌊(k0 : ℝ) * (n : ℝ)⌋ = (k0 : ℤ) * (n : ℤ) := by
  rw [← Int.cast_natCast (n := k0), ← Int.cast_natCast (n := n), ← Int.cast_mul]
  exact Int.floor_intCast _

/-- Uniform lower bound `β (γ/2)^(k₀ - 1)` for all translated long-way crossings of `k₀n × n` and
`n × k₀n` rectangles under `ℙ_{1/2}`, from the hypotheses listed in the module docstring. -/
theorem bxr_uniform_seed
    (hpa : PositivelyAssociated halfMeasure)
    {k0 : ℕ} (hk0 : 2 ≤ k0) {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hmeasH : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
    (hmeasV : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)))
    (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross halfMeasure n 1)
    (h2box : ∀ n : ℤ, 0 < n →
      γ ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 n 0 n))
    (hrefl : ∀ n : ℤ, 0 < n →
      halfMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = halfMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
    (∀ (n : ℕ) (τ : Site 2), 1 ≤ n →
        β * ((1 / 2) * γ) ^ (k0 - 1)
          ≤ halfMeasure.real
              (translatedHorizontalCrossingEvent τ ⌊(k0 : ℝ) * (n : ℝ)⌋ (n : ℤ)))
      ∧ (∀ (n : ℕ) (τ : Site 2), 1 ≤ n →
        β * ((1 / 2) * γ) ^ (k0 - 1)
          ≤ halfMeasure.real
              (translatedVerticalCrossingEvent τ (n : ℤ) ⌊(k0 : ℝ) * (n : ℝ)⌋)) := by
  have hk1 : 1 ≤ k0 := le_trans (by norm_num) hk0
  have hbase : ∀ n : ℤ, 0 < n →
      β * ((1 / 2) * γ) ^ (k0 - 1) ≤ rai_cross halfMeasure n k0 := by
    intro n hn
    exact rai_cross_lb halfMeasure hpa hn hβ hγ (hseed n hn)
      (cti_h2box_discharge (hmeas2box n hn) (h2box n hn))
      (cti_hband_discharge (hmeasband n hn) (hband n hn)) k0 hk1
  refine ⟨?_, ?_⟩
  · intro n τ hn1
    have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    rw [bxr_floor_natMul,
      bxr_translatedHorizontalCrossing_invariant τ ((k0 : ℤ) * (n : ℤ)) (n : ℤ)
        (hmeasH (n : ℤ) hn)]
    have := hbase (n : ℤ) hn
    rwa [rai_cross_def] at this
  · intro n τ hn1
    have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    rw [bxr_floor_natMul,
      bxr_translatedVerticalCrossing_invariant τ (n : ℤ) ((k0 : ℤ) * (n : ℤ))
        (hmeasV (n : ℤ) hn), hrefl (n : ℤ) hn]
    have := hbase (n : ℤ) hn
    rwa [rai_cross_def] at this

/-- The box-crossing property of `ℙ_{1/2}` with integer aspect ratio `k₀ ≥ 2`, conditional on
positive
association `hpa`, the square bound `hseed`, the RSW bound `h2box` on `2n × n` crossings and the
band bound `hband`; the measurability and reflection hypotheses are provable
(`measurableSet_horizontalCrossingEvent`, `crf_hrefl_fixed`). -/
theorem bxr_boxCrossingProperty
    (hpa : PositivelyAssociated halfMeasure)
    {k0 : ℕ} (hk0 : 2 ≤ k0) {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hmeasH : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
    (hmeasV : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)))
    (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross halfMeasure n 1)
    (h2box : ∀ n : ℤ, 0 < n →
      γ ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 n 0 n))
    (hrefl : ∀ n : ℤ, 0 < n →
      halfMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = halfMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
    BoxCrossingProperty halfMeasure (k0 : ℝ) := by
  obtain ⟨hHseed, hVseed⟩ :=
    bxr_uniform_seed hpa hk0 hβ hγ hmeas2box hmeasband hmeasH hmeasV hseed h2box hband hrefl
  have hρ : (1 : ℝ) < (k0 : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hk0
  have hc : (0 : ℝ) < β * ((1 / 2) * γ) ^ (k0 - 1) := by positivity
  exact rba_bxp_of_uniform_seed halfMeasure (k0 : ℝ) hρ 1
    (β * ((1 / 2) * γ) ^ (k0 - 1)) hc
    (fun n τ hn => hHseed n τ hn) (fun n τ hn => hVseed n τ hn)

end Universality

end StatMech
