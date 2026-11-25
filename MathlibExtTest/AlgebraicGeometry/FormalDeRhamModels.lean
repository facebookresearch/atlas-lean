/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.FormalDeRhamModels
import MathlibExt.AlgebraicGeometry.SyntomicNearbyComparisons

/-! Regressions for the shape of the formal de Rham and syntomic models: why the multiplicative
de Rham hypermodels are not injective, that the formal syntomic cochains are derived, and that the
Nygaard K-injective toolbox is the generic record.
-/

open CategoryTheory

/-- The level-zero obstruction behind `FormalDeRhamModels.System`: a `p`-divisible module (such as
an injective `ℤ_p`-module) carrying a left-unital bilinear product whose unit is killed by `p` is
zero. A de Rham hypermodel of a level killed by `p` therefore cannot be both injective and
strictly multiplicative, so the multiplicative hypermodel is only acyclic for global sections. -/
example {R J : Type} [CommRing R] [AddCommGroup J] [Module R J] (μ : J →ₗ[R] J →ₗ[R] J) (e : J)
    (r : R) (hunit : ∀ x, μ e x = x) (he : r • e = 0) (hdiv : ∀ x : J, ∃ y, x = r • y) (x : J) :
    x = 0 := by
  obtain ⟨y, rfl⟩ := hdiv x
  calc r • y = r • μ e y := by rw [hunit]
    _ = μ (r • e) y := by rw [map_smul, LinearMap.smul_apply]
    _ = 0 := by rw [he, map_zero, LinearMap.zero_apply]

namespace FormalDeRhamModelsTest

open MathlibExt.AlgebraicGeometry
open FormalGenericFibreModels FormalSyntomicSiteModels PrismaticSyntomicModels
open AbsolutePrismaticBasis PrismaticFilteredTwists

/-- The formal syntomic cochains restrict a K-injective resolution of the extended complex, not
the extended complex itself. -/
example (p : ℕ) [Fact p.Prime] (C : CompletePadicField p) (B : IntegralBase p C)
    [(basisInclusion p C B).IsContinuous (AbsolutePrismaticBasis.topology p B.ring)
      (QuasiSyntomicPrismSites.topology p B.ring)]
    {D : ∀ S : AbsolutePrismaticBasis.Basis p B.ring,
      InitialLift p (AbsolutePrismaticBasis.ring p S)}
    {Z : ZeroReduction p B.ring D} {T : TwistTower p B.ring D Z} {F : FrobeniusModel p B.ring D Z T}
    {X : FormalScheme p C} (R : FormalRestriction p C B X) (Q : QsynExtension p C B D Z T F)
    (RQ : MathlibExt.FunctorialKInjective (QsynSheaves p C B)) (i : ℤ) :
    R.syntomic Q RQ i = (R.functor.mapHomologicalComplex (.up ℤ)).obj (RQ.functor.obj (Q.complex i)) :=
  rfl

/-- The Nygaard K-injective toolbox is the generic functorial K-injective record. -/
example (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p) :
    PrismaticNygaardCohomology.Resolution p A =
      MathlibExt.FunctorialKInjective (PrismaticNygaardCohomology.Sheaves p A) :=
  rfl

end FormalDeRhamModelsTest
