/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace

@[expose] public section

/-!
# Projectivity and normalized rational direct images

Projectivity over `ℂ` and projective space `ℙⁿ_ℂ` are those of
`MathlibExt.AlgebraicGeometry.ProjectiveSpace` over the complex numbers: a
closed immersion into some `ℙⁿ_ℂ` that respects the structure morphism. The
normalized direct image uses Mathlib's derived pushforward on the analytic
topological spaces of complex points: `ℚ_X[n]` places the rational constant
sheaf in cohomological degree `-n`.

The declarations live in the namespace
`MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted`, shared
with the requests that use them; this module itself is complete and requests
nothing.

## Reference

M. A. A. de Cataldo and L. Migliorini, *The Hodge theory of algebraic maps*,
Ann. Sci. École Norm. Sup. (4) 38 (2005), no. 5, 693–750,
§§3.2–3.3 and Theorem 2.1.1. https://arxiv.org/abs/math/0306030
-/

namespace MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Projectivity over `ℂ`: a closed immersion over `ℂ` into some projective
space, `ProjectiveSpace.IsProjective` over the complex numbers. -/
abbrev IsProjectiveOverC (X : ComplexScheme) : Prop :=
  ProjectiveSpace.IsProjective X

/-- Projective space `ℙⁿ_ℂ`, as a scheme over `ℂ`: `ProjectiveSpace.projectiveSpace`
over the complex numbers. -/
abbrev projectiveSpace (n : ℕ) : ComplexScheme :=
  ProjectiveSpace.projectiveSpace ℂ n

/-- Projective space is projective over `ℂ`, through the identity. -/
theorem isProjectiveOverC_projectiveSpace (n : ℕ) : IsProjectiveOverC (projectiveSpace n) :=
  ⟨n + 1, 𝟙 _, show IsClosedImmersion (𝟙 _) from inferInstance, (Category.id_comp _).symm⟩

/-- The rational normalized direct image `Rf_* ℚ_X[n]`, with the constant sheaf
placed in degree `-n`: `ConstructibleComplexes.normalizedDirectImage` at
`k = ℚ`. -/
abbrev normalizedDirectImage (X Y : ComplexScheme) (f : X ⟶ Y) (n : ℕ) :
    RationalDerived (space Y) :=
  ConstructibleComplexes.normalizedDirectImage ℚ X Y f n

end

end MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted
