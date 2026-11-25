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
open MathlibExt.AlgebraicGeometry MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted

namespace MathlibExtTest.AlgebraicGeometry.ProjectiveDirectImage

attribute [local instance] HasDerivedCategory.standard

/-- `ℙⁿ_ℂ` is projective over `ℂ`, through the identity closed immersion. -/
example (n : ℕ) : ProjectiveSpace.IsProjective (ProjectiveSpace.projectiveSpace ℂ n) :=
  isProjective_projectiveSpace n

/-- The normalized direct image places the constant sheaf in degree `-n`
before deriving the pushforward. -/
example (X Y : ComplexScheme) (f : X ⟶ Y) (n : ℕ) :
    ConstructibleComplexes.normalizedDirectImage ℚ X Y f n =
      DerivedCategory.Plus.ι.obj
        (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (spaceMap f)).rightDerivedFunctorPlus).obj
          ((DerivedCategory.Plus.singleFunctor (RationalSheaf (space X)) (-(n : ℤ))).obj
            (rationalConstantSheaf (space X)))) :=
  rfl

end MathlibExtTest.AlgebraicGeometry.ProjectiveDirectImage

end
