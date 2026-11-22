/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import MathlibExt.Analysis.Variational.VariationalConvexity

@[expose] public section

namespace MathlibExtTest.Analysis.Variational.VariationalConvexity

open MetaMathlibExt

-- Algebra 373: Rank-One Convexity

theorem IsRankOneConvex.convexOn_rankOneLine
    {W : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hW : IsRankOneConvex W)
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : B.rank = 1) :
    ConvexOn ℝ Set.univ
      (fun t : ℝ => W (A + t • B)) := by
  exact hW A B hB

-- Algebra 374: Morrey Quasiconvexity

theorem IsMorreyQuasiconvex.inequality
    {W : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hW : IsMorreyQuasiconvex W)
    (Ω : Set (EuclideanSpace ℝ (Fin 2)))
    (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (K : TopologicalSpace.Compacts
      (EuclideanSpace ℝ (Fin 2)))
    (hK : (↑K : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω)
    (φ : ContDiffMapSupportedIn
      (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 2)) ⊤ K) :
    (MeasureTheory.volume Ω).toReal * W A ≤
      ∫ x in Ω,
        W
          (A +
            ((Matrix.toEuclideanCLM :
              Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
                (EuclideanSpace ℝ (Fin 2) →L[ℝ]
                  EuclideanSpace ℝ (Fin 2))).symm
              (fderiv ℝ
                (φ :
                  EuclideanSpace ℝ (Fin 2) →
                    EuclideanSpace ℝ (Fin 2))
                x))) := by
  exact hW Ω hΩopen hΩbounded A K hK φ

-- Algebra 375: Burkholder Integrand

theorem burkholderIntegrand_two
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderIntegrand 2 A = A.det := by
  simp [burkholderIntegrand]

end MathlibExtTest.Analysis.Variational.VariationalConvexity

end
