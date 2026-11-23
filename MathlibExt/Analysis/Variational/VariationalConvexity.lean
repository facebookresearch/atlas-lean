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

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Algebra 373, Algebra 374, Algebra 375

/-!
# Rank-One Convexity; Morrey Quasiconvexity; Burkholder Integrand

## References

* This is the standard definition of rank-one convexity used in the calculus of variations. See,
  for example: V. Sverak, Rank-One Convexity Does Not Imply Quasiconvexity, Proceedings of the
  Royal Society of Edinburgh Section A, 120 (1992), 185-189.
  https://doi.org/10.1017/S0308210500015080, See also: J. Voss, R. J. Martin, O. Sander et al.,
  Numerical Approaches for Investigating Quasiconvexity in the Context of Morrey's Conjecture,
  Journal of Nonlinear Science 32 (2022), 77. https://doi.org/10.1007/s00332-022-09820-x (for
  `IsRankOneConvex`)
* Quasiconvexity in this variational sense was introduced by Morrey: C. B. Morrey, Quasi-convexity
  and the Lower Semicontinuity of Multiple Integrals, Pacific Journal of Mathematics 2 (1952),
  25-53. https://doi.org/10.2140/pjm.1952.2.25, See also: V. Sverak, Rank-One Convexity Does Not
  Imply Quasiconvexity, Proceedings of the Royal Society of Edinburgh Section A 120 (1992),
  185-189. https://doi.org/10.1017/S0308210500015080 (for `IsMorreyQuasiconvex`)
* See: K. Astala, T. Iwaniec, I. Prause and E. Saksman, Burkholder Integrals, Morrey's Problem and
  Quasiconformal Mappings, Journal of the American Mathematical Society 25 (2012), 507-531.
  https://doi.org/10.1090/S0894-0347-2011-00718-2, See also: A. Guerra and J. Kristensen,
  Automatic Quasiconvexity of Homogeneous Isotropic Rank-One Convex Integrands, Archive for
  Rational Mechanics and Analysis 245 (2022), 479-500. https://doi.org/10.1007/s00205-022-01792-2
  (for `burkholderIntegrand`)
-/

namespace MetaMathlibExt

-- Algebra 373: Rank-One Convexity

/-- Let

W:ℝ^{2×2}→ℝ.

The function W is rank-one convex if for every

A,B∈ℝ^{2×2}

such that

rank(B)=1,

the function

t↦ W(A+tB)

is convex on ℝ.
-/
def IsRankOneConvex
    (W : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
    B.rank = 1 →
      ConvexOn ℝ Set.univ
        (fun t : ℝ => W (A + t • B))

-- Algebra 374: Morrey Quasiconvexity

/-- Let

W:ℝ^{2×2}→ℝ.

The function W is quasiconvex in the sense of Morrey if, for every bounded open set

Ω⊂ℝ²,

every

A∈ℝ^{2×2},

and every smooth compactly supported function

φ∈ C_c^∞(Ω;ℝ²),

one has

W(A)≤1/(|Ω|) ∫_Ω W(A+Dφ(x)) dx.

Equivalently,

|Ω|W(A) ≤ ∫_Ω W(A+Dφ(x)) dx.

The Lean definition uses this latter, unnormalized form.
-/
noncomputable def IsMorreyQuasiconvex
    (W : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ Ω : Set (EuclideanSpace ℝ (Fin 2)),
    IsOpen Ω →
    Bornology.IsBounded Ω →
    ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      ∀ K : TopologicalSpace.Compacts
        (EuclideanSpace ℝ (Fin 2)),
        (↑K : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω →
        ∀ φ : ContDiffMapSupportedIn
          (EuclideanSpace ℝ (Fin 2))
          (EuclideanSpace ℝ (Fin 2)) ⊤ K,
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
                      x)))

-- Algebra 375: Burkholder Integrand

/-- For p≥2 and

A∈ℝ^{2×2},

define the Burkholder integrand by

Bₚ(A)=[(1-2/p)|A|²+det A]|A|ᵖ⁻²,

where |A| denotes the Euclidean operator norm of A.
-/
noncomputable def burkholderIntegrand
    (p : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  let opNorm : ℝ :=
    ‖(Matrix.toEuclideanCLM (n := Fin 2)).toFun A‖
  (((1 : ℝ) - 2 / p) * opNorm ^ 2 + A.det) *
    Real.rpow opNorm (p - 2)

end MetaMathlibExt

end
