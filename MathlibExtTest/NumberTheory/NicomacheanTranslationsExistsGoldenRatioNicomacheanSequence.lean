/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NicomacheanTranslationsExistsGoldenRatioNicomacheanSequence

/-! # Tests for golden-ratio Nicomachean sequences -/

namespace MathlibExtTest.NumberTheory.NicomacheanTranslationsExistsGoldenRatioNicomacheanSequence

open MetaMathlibExt

-- At `N = 1` the sequence contains `φ⁻¹` and has zero defect.
example : ∃ σ : List ℝ, Real.goldenRatio⁻¹ ∈ σ ∧ nicomacheanNu σ = 0 := by
  obtain ⟨σ, _, _, hnu, hmem⟩ := exists_goldenRatio_nicomachean_sequence 1
  have h1mem : Real.goldenRatio⁻¹ ^ 1 ∈ σ := hmem 1 (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  have h1 : Real.goldenRatio⁻¹ ∈ σ := by simpa using h1mem
  exact ⟨σ, h1, hnu⟩

-- At `N = 2` the sequence contains the first two inverse powers.
example : ∃ σ : List ℝ, Real.goldenRatio⁻¹ ∈ σ ∧ Real.goldenRatio⁻¹ ^ 2 ∈ σ := by
  obtain ⟨σ, _, _, _, hmem⟩ := exists_goldenRatio_nicomachean_sequence 2
  have h1mem : Real.goldenRatio⁻¹ ^ 1 ∈ σ := hmem 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have h1 : Real.goldenRatio⁻¹ ∈ σ := by simpa using h1mem
  exact ⟨σ, h1, hmem 2 (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)⟩

-- At `N = 1` the sequence has an irrational entry.
example : ∃ σ x, x ∈ σ ∧ Irrational x ∧ nicomacheanNu σ = 0 := by
  obtain ⟨σ, _, htau, hnu, hmem⟩ := exists_goldenRatio_nicomachean_sequence 1
  obtain ⟨τ, hsub, hlen, hirr⟩ := htau
  have h1mem : Real.goldenRatio⁻¹ ^ 1 ∈ σ := hmem 1 (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  have hmem1 : Real.goldenRatio⁻¹ ∈ σ := by simpa using h1mem
  have hpos_len : 0 < σ.length := List.length_pos_of_mem hmem1
  have htau_pos : 0 < τ.length := by omega
  obtain ⟨x, hx_tau⟩ := List.exists_mem_of_length_pos htau_pos
  exact ⟨σ, x, List.Sublist.mem hx_tau hsub, hirr x hx_tau, hnu⟩

end MathlibExtTest.NumberTheory.NicomacheanTranslationsExistsGoldenRatioNicomacheanSequence
