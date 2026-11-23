/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjectiveDirectImage

@[expose] public section

/-! # Tests for `MathlibExt.AlgebraicGeometry.ProjectiveDirectImage` -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted

namespace MathlibExtTest.AlgebraicGeometry.ProjectiveDirectImage

attribute [local instance] HasDerivedCategory.standard MvPolynomial.gradedAlgebra

/-- Projective space `ℙⁿ_ℂ`, as a scheme over `ℂ`. -/
abbrev projectiveSpace (n : ℕ) : ComplexScheme :=
  Over.mk (gradedProjToSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ))

/-- `ℙⁿ_ℂ` is projective over `ℂ`, through the identity closed immersion. -/
example (n : ℕ) : IsProjectiveOverC (projectiveSpace n) :=
  ⟨n, 𝟙 _, inferInstance, (Category.id_comp _).symm⟩

/-- The normalized direct image places the constant sheaf in degree `-n`
before deriving the pushforward. -/
example (X Y : ComplexScheme) (f : X ⟶ Y) (n : ℕ) :
    normalizedDirectImage X Y f n =
      DerivedCategory.Plus.ι.obj
        (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (spaceMap f)).rightDerivedFunctorPlus).obj
          ((DerivedCategory.Plus.singleFunctor (RationalSheaf (space X)) (-(n : ℤ))).obj
            (rationalConstantSheaf (space X)))) :=
  rfl

end MathlibExtTest.AlgebraicGeometry.ProjectiveDirectImage

end
