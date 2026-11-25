/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.OrthogonalPolynomialHilbertBasis

open MeasureTheory
open MathlibExt.Analysis.InnerProductSpace.OrthogonalPolynomialHilbertBasisWanted
  (orthogonalPolynomial_hilbertBasis)

/-- In the same Hilbert basis, the first two vectors have constant and linear representatives,
respectively, and are orthonormal. -/
example :
    ∃ B : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Set.Icc (-1 : ℝ) 1))),
      Orthonormal ℝ B ∧
      ∃ q₀ q₁ : Polynomial ℝ, q₀.natDegree = 0 ∧ q₁.natDegree = 1 ∧
        ∀ᵐ x ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)),
          (B 0) x = Polynomial.aeval x q₀ ∧ (B 1) x = Polynomial.aeval x q₁ := by
  obtain ⟨B, hB⟩ := orthogonalPolynomial_hilbertBasis
  obtain ⟨q₀, hd₀, h₀⟩ := hB 0
  obtain ⟨q₁, hd₁, h₁⟩ := hB 1
  exact ⟨B, B.orthonormal, q₀, q₁, hd₀, hd₁, h₀.and h₁⟩
