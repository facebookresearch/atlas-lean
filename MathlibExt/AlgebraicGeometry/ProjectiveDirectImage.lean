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
# Projectivity of complex projective space

Projectivity over `ℂ` and projective space `ℙⁿ_ℂ` are
`ProjectiveSpace.IsProjective` and `ProjectiveSpace.projectiveSpace ℂ` (a closed
immersion into some `ℙⁿ_ℂ` respecting the structure morphism), and the rational
normalized direct image `Rf_* ℚ_X[n]` is `ConstructibleComplexes.normalizedDirectImage ℚ`.
This module records that `ℙⁿ_ℂ` is projective, in the namespace
`MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted` shared with the
requests that use it; it is complete and requests nothing.

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

/-- Projective space is projective over `ℂ`, through the identity. -/
theorem isProjective_projectiveSpace (n : ℕ) :
    ProjectiveSpace.IsProjective (ProjectiveSpace.projectiveSpace ℂ n) :=
  ⟨n + 1, 𝟙 _, show IsClosedImmersion (𝟙 _) from inferInstance, (Category.id_comp _).symm⟩

end

end MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted
