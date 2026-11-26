/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.BernsteinFourierSupportLpLq

open MeasureTheory
open scoped ENNReal FourierTransform
open MathlibExt.Analysis.Fourier.BernsteinFourierSupportLpLqWanted

-- The finite-exponent estimate uses the difference of reciprocal exponents.
example {n : ℕ} :
    ∃ C > (0 : ℝ), ∀ E : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet E → volume E < ⊤ →
      ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, tsupport (fun ξ ↦ (𝓕 f) ξ) ⊆ E →
        ‖f.toLp 3‖ ≤ C * (volume E).toReal ^ (1 / 3 : ℝ) * ‖f.toLp (3 / 2)‖ := by
  obtain ⟨C, hC, h⟩ :=
    exists_const_norm_toLp_le_volume_rpow_mul_norm_toLp_of_tsupport_fourier_subset (n := n)
  refine ⟨C, hC, fun E hE hvol f hs ↦ ?_⟩
  have hest := h E hE hvol (3 / 2) 3 (by norm_num [ENNReal.le_div_iff_mul_le])
    (by norm_num [ENNReal.div_le_iff]) le_top (by norm_num [ENNReal.div_le_iff]) f hs
  norm_num [ENNReal.toReal_div] at hest ⊢
  exact hest

-- At q = ∞, a Fourier support contained in a null set forces the essential supremum to vanish.
example {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))} (hE : MeasurableSet E)
    (hvol : volume E = 0) (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (hs : tsupport (fun ξ ↦ (𝓕 f) ξ) ⊆ E) : ‖f.toLp ⊤‖ = 0 := by
  obtain ⟨C, _, h⟩ :=
    exists_const_norm_toLp_le_volume_rpow_mul_norm_toLp_of_tsupport_fourier_subset (n := n)
  have hest := h E hE (by simp [hvol]) 2 ⊤ (by norm_num) le_top le_rfl le_rfl f hs
  apply le_antisymm _ (norm_nonneg _)
  simpa [hvol] using hest
