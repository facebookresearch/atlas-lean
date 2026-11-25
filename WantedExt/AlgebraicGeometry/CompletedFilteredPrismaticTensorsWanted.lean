/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors

/-!
# Completed filtered prismatic tensor construction requests

The coefficient rings, signed finite words, relative tensor, dual
evaluation, coefficient transitions and all finite completion maps are
fixed native operations. The derived limit resolves the actual finite
tower before taking products. These endpoints certify that finite
tensor/evaluation recipe and its native projection comparisons.

No unfiltered tensor inversion or raw-product derived-limit equivalence
is requested. The source inverse is realized in the completion of the
actual filtered quotient tower.

Source: BMS19 arXiv:1802.03261v2, Theorem1.12(3), footnote3,
Sections5.1/7.3/7.4; Bhatt–Scholze arXiv:1905.08229v4,
Sections12–15.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry AbsolutePrismaticBasis PrismaticFilteredTwists
open SyntomicNearbyComparisons CompletedFilteredPrismaticTensors
open MathlibExt (FunctorialKInjective)

attribute [local instance] HasDerivedCategory.standard

public def_wanted prismaticKInjectiveResolution
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p) :
    FunctorialKInjective (PrismaticNygaardCohomology.Sheaves p A)

/-- The fixed quotient-tensor transition is the original semilinear
dual/line transition on every actual pure tensor. -/
public theorem_wanted finiteTensorTransition
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z) :
    TensorTransitionNormalization p A D Z T

/-- Construct the commuting squares for the fixed finite
sheafification counit inverse and K-injective resolution unit. -/
public def_wanted finiteCompletionMaps
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z)
    (R : FunctorialKInjective (PrismaticNygaardCohomology.Sheaves p A)) :
    CompletionMaps p A D Z T R

/-- The source filtered inverse evaluation is an isomorphism after
the native derived-limit realization, with every finite projection and
the actual source-completion comparison normalized. -/
public theorem_wanted completedFilteredInverse
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z)
    (R : FunctorialKInjective (PrismaticNygaardCohomology.Sheaves p A))
    (C : CompletionMaps p A D Z T R) :
    CompletedFilteredInverse p A D Z T R C

end WantedExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors
