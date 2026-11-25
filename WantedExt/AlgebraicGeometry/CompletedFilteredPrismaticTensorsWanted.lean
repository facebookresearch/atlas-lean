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

/-- For a prime $p$, a quasisyntomic ring `A` with chosen initial prisms `D` over the semiperfectoid
basis of its site, a zero reduction `Z` and a twist tower `T` (finite filtered Breuil–Kisin lines
$L_n$ and their duals $L_n^\vee$ over the finite quotient coefficient rings): the transition from
level $n + 1$ to level $n$ of the tensor products $L_n^\vee \otimes L_n$, obtained from the
weight-zero transition of `T` through the evaluation isomorphisms, sends every pure tensor
$f \otimes x$ to $f' \otimes x'$, where $f'$ and $x'$ are the images of $f$ and $x$ under the dual
and line transitions. -/
public theorem_wanted finiteTensorTransition
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z) :
    TensorTransitionNormalization p A D Z T

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

/-- Completed filtered inverse: for a prime $p$, a quasisyntomic ring `A` with chosen initial prisms
`D`, a zero reduction `Z`, a twist tower `T`, a functorial K-injective resolution `R` and commuting
finite completion maps `C`: the completed evaluation map, from the derived limit (the Milnor limit
of the resolved tower) of the finite tensor products $L_n^\vee \otimes L_n$ to the derived limit of
the weight-zero tower, is an isomorphism in the derived category; it commutes with the projections
to every finite level, where it is the resolved finite evaluation; and for every weight $i$, the
comparison map from the completed twist of weight $i$ to the derived limit of its resolved finite
tower commutes with the projections to every level and the finite completion maps. -/
public theorem_wanted completedFilteredInverse
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z)
    (R : FunctorialKInjective (PrismaticNygaardCohomology.Sheaves p A))
    (C : CompletionMaps p A D Z T R) :
    CompletedFilteredInverse p A D Z T R C

end WantedExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors
