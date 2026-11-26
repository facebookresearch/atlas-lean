/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors
public import MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensorsFiniteTensorTransition
public import MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensorsCompletedFilteredInverse

/-!
# Completed filtered prismatic tensor construction requests

The coefficient rings, signed finite words, relative tensor, dual
evaluation, coefficient transitions and all finite completion maps are
fixed native operations. The derived limit resolves the actual finite
tower before taking products. These endpoints, together with
`finiteTensorTransition` (now proved in
`MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensorsFiniteTensorTransition`)
and `completedFilteredInverse` (now proved in
`MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensorsCompletedFilteredInverse`),
certify that finite tensor/evaluation recipe and its native projection
comparisons.

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

/-- For a prime $p$, a quasisyntomic ring `A` with chosen initial prisms `D`, a zero reduction `Z`,
a twist tower `T` and a functorial K-injective resolution `R` of sheaves on its site: for every
weight $i$ and level $n$, the finite completion maps (from the level-$n$ twist sheaf of weight $i$
in degree zero to the K-injective resolution of its sheafification: the inverse of the
sheafification counit followed by the unit of `R`) commute with the transition maps from level
$n + 1$ to level $n$. -/
public def_wanted finiteCompletionMaps
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z)
    (R : FunctorialKInjective (PrismaticNygaardCohomology.Sheaves p A)) :
    CompletionMaps p A D Z T R

end WantedExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors
