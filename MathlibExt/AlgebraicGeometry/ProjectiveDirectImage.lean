/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The projectivity definitions are adapted from
`WantedExt/AlgebraicGeometry/TopologicalReconstructionWanted.lean` in ATLAS
at commit 841d5b685836b986f0bb29cd63fd2300f957e849. That file attributes
`LeanEval.AlgebraicGeometry.TopologicalReconstruction` in leanprover/lean-eval
at commit 38361be884302c7edce1908c4aef8296eb2cb27e, distributed under the
Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Modification notice: renamed the graded structure morphism, specialized the
projectivity predicate to schemes over `ℂ`, and used `n + 1` homogeneous
coordinates for `ℙⁿ`.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import MathlibExt.AlgebraicGeometry.PerverseSheaves

@[expose] public section

/-!
# Projectivity and normalized rational direct images

Projectivity over `ℂ` is expressed by a closed immersion into some `ℙⁿ_ℂ`
that respects the structure morphism. The normalized direct image uses
Mathlib's derived pushforward on the analytic topological spaces of complex
points: `ℚ_X[n]` places the rational constant sheaf in cohomological degree
`-n`.

The projective decomposition and semisimplicity requests are in
`WantedExt/AlgebraicGeometry/DeCataldoMiglioriniDecompositionWanted.lean`.

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

/-- The structure morphism of the projective spectrum of a graded algebra.
This is the same projective-over-a-field construction used by
`WantedExt/AlgebraicGeometry/TopologicalReconstructionWanted.lean`. -/
def gradedProjToSpec {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ..))

/-- Projectivity over `ℂ`, expressed by a closed immersion into some `ℙⁿ_ℂ`.
The equation requires the immersion to respect the structure morphism. -/
def IsProjectiveOverC (X : ComplexScheme) : Prop :=
  let := @MvPolynomial.gradedAlgebra
  ∃ (n : ℕ)
    (i : X.left ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)),
    IsClosedImmersion i ∧ X.hom = i ≫ gradedProjToSpec _

/-- The actual derived direct image of the rational constant sheaf placed
in degree `-n`, namely `Rf_* ℚ_X[n]`. -/
def normalizedDirectImage (X Y : ComplexScheme) (f : X ⟶ Y) (n : ℕ) :
    RationalDerived (space Y) :=
  DerivedCategory.Plus.ι.obj
    (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ)
      (spaceMap f)).rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor (RationalSheaf (space X))
          (-(n : ℤ))).obj (rationalConstantSheaf (space X))))

end

end MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted
