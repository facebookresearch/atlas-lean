/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.BXPAllAspect
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LeftFillInteriorArc
public import MathlibExt.Probability.Percolation.Universality.CrossingReflection
public import MathlibExt.Probability.Percolation.Universality.RSWBandBound

/-!
# Box-crossing property at p = 1/2 from a minimal hypothesis

The box-crossing property for critical bond percolation on `ℤ²` from the square-crossing
self-duality and one lower bound on long-rectangle crossings.

## i. Overview

Self-duality of `halfMeasure` gives probability `1/2` for crossing a square
(`bmh_square_seed_half`), and the face-dual construction of `LeftFillInteriorArc` gives the same
without a separation hypothesis (`*_faithful`). The headlines `bmh_boxCrossingProperty_selfDual` and
`bmh_boxCrossingProperty_selfDual_faithful` are conditional: they assume positive association `hpa`,
measurability of the crossing events, and the RSW input `h2box : 1/8 ≤ P(horizontal crossing of a 2n
× n box)`. The `_faithful` version drops the square-separation hypothesis of the first.

## ii. Key results

- `bmh_square_seed_half_faithful`: square crossing probability is at least `1/2` (measurability
  hypotheses only).
- `bmh_boxCrossingProperty_selfDual_faithful`: BXP for every aspect ratio, conditional on `hpa`,
  measurability and `h2box`.

## iii. Table of contents

- A. Square seeds
- B. Box-crossing property

## iv. References

* H. Kesten, *The critical probability of bond percolation on the square lattice equals 1/2*, Comm.
  Math. Phys. 74 (1980).
* L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978); P. D. Seymour, D. J. A.
  Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete Math. 3 (1978).
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-! ## A. Square seeds -/

lemma bmh_square_reflection (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n)) :
    halfMeasure.real (verticalCrossingEvent 0 n 0 n)
      = halfMeasure.real (horizontalCrossingEvent 0 n 0 n) :=
  crf_verticalCrossing_eq_horizontal_swap 0 n 0 n hmeasH

lemma bmh_square_seed_half (n : ℤ) (_hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) :
    (1 : ℝ) / 2 ≤ rai_cross halfMeasure n 1 := by
  rw [rai_cross_def]
  have h1n : ((1 : ℕ) : ℤ) * n = n := by push_cast; ring
  rw [h1n]
  exact rba_self_dual_square_half n hmeasH hmeasV hsep (bmh_square_reflection n hmeasH)

lemma bmh_band_seed_half (n : ℤ) (_hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) :
    (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 n 0 n) :=
  rbb_band_crossing_lb 0 n 0 n hmeasH hmeasV hsep (bmh_square_reflection n hmeasH)

lemma bmh_square_seed_half_faithful (n : ℤ) (hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    (1 : ℝ) / 2 ≤ rai_cross halfMeasure n 1 := by
  rw [rai_cross_def]
  have h1n : ((1 : ℕ) : ℤ) * n = n := by push_cast; ring
  rw [h1n]
  exact crr_square_half n hn hmeasH hmeasFace hmeasThin

lemma bmh_band_seed_half_faithful (n : ℤ) (hn : 0 < n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 n 0 n) := by
  rw [bmh_square_reflection n hmeasH]
  exact crr_square_half n hn hmeasH hmeasFace hmeasThin

/-! ## B. Box-crossing property -/

/-- The box-crossing property at `p = 1/2` for every aspect ratio `ρ > 1`, conditional on `hpa`,
  measurability and `h2box`. -/
theorem bmh_boxCrossingProperty_selfDual
    (hpa : PositivelyAssociated halfMeasure)
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hsepSquare : ∀ n : ℤ, 0 < n →
      (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
    (h2box : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 8 ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n)) :
    ∀ ρ : ℝ, 1 < ρ → BoxCrossingProperty halfMeasure ρ := by
  apply bxa_boxCrossingProperty_all hpa (β := 1 / 2) (γ := 1 / 8)
    (by norm_num) (by norm_num)
  · intro n hn
    exact hmeasGenH (2 * n) n (by omega) hn
  · intro n hn
    exact hmeasGenV n n hn hn
  · exact hmeasGenH
  · exact hmeasGenV
  · intro n hn
    exact bmh_square_seed_half n hn (hmeasGenH n n hn hn) (hmeasGenV n n hn hn)
      (hsepSquare n hn)
  · exact h2box
  · intro n hn
    exact bmh_band_seed_half n hn (hmeasGenH n n hn hn) (hmeasGenV n n hn hn)
      (hsepSquare n hn)
  · exact crf_hrefl (fun k0 hk0 n hn =>
      hmeasGenH ((k0 : ℤ) * n) n (by positivity) hn)

/-- BXP for every aspect ratio, conditional on `hpa`, measurability and `h2box`. -/
theorem bmh_boxCrossingProperty_selfDual_faithful
    (hpa : PositivelyAssociated halfMeasure)
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1)))
    (h2box : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 8 ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n)) :
    ∀ ρ : ℝ, 1 < ρ → BoxCrossingProperty halfMeasure ρ := by
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
