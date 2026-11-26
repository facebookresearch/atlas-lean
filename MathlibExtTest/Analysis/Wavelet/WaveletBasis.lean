/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Wavelet.WaveletBasis

/-!
# Tests for the wavelet orthonormal basis

Applying the wavelet basis theorem to an arbitrary multiresolution approximation: the
scale-zero atom is a unit vector, orthogonal to its unit translate, almost everywhere equal
to the wavelet, and it lies in the next resolution space and its orthogonal complement.
-/

open MeasureTheory
open scoped InnerProductSpace
open MathlibExt.Analysis.Wavelet.Multiresolution
open MathlibExt.Analysis.Wavelet.MultiresolutionWanted

example {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) :
    ∃ ψ : Lp ℂ 2 (volume : Measure ℝ),
      ∃ b : HilbertBasis (ℤ × ℤ) ℂ (Lp ℂ 2 (volume : Measure ℝ)),
        (∀ jk : ℤ × ℤ, ⇑(b jk : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
          fun x => ((Real.sqrt ((2 : ℝ) ^ jk.1) : ℝ) : ℂ) * ψ ((2 : ℝ) ^ jk.1 * x - jk.2)) ∧
        ‖b (0, 0)‖ = 1 ∧ ⟪b (0, 0), b (0, 1)⟫_ℂ = 0 ∧
        b (0, 0) ∈ V 1 ∧ b (0, 0) ∈ (V 0)ᗮ ∧ ⇑(b (0, 0)) =ᵐ[volume] fun x => ψ x := by
  obtain ⟨ψ, b, hae, hmem⟩ := exists_wavelet_hilbertBasis hV
  refine ⟨ψ, b, hae, b.orthonormal.1 _, b.orthonormal.2 (by decide), ?_, ?_, ?_⟩
  · have h00 := hmem 0 0
    simpa using h00.1
  · simpa using (hmem 0 0).2
  · simpa using hae (0, 0)
