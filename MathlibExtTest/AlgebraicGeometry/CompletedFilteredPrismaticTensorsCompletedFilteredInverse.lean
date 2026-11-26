/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors
import MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensorsCompletedFilteredInverse

/-!
# Tests for the completed filtered inverse

The completed evaluation map is an isomorphism; it commutes with the
projections at levels zero and one, in both directions; the comparison maps
commute with the projections at weights one and negative one and positive
levels.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.CompletedFilteredPrismaticTensorsCompletedFilteredInverse

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry AbsolutePrismaticBasis PrismaticFilteredTwists
open SyntomicNearbyComparisons CompletedFilteredPrismaticTensors
open MathlibExt (FunctorialKInjective)
open WantedExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
  (D : ∀ B : Basis p A, InitialLift p (ring p B))
  (Z : ZeroReduction p A D) (T : TwistTower p A D Z)
  (R : FunctorialKInjective (PrismaticNygaardCohomology.Sheaves p A))
  (C : CompletionMaps p A D Z T R)

example : IsIso (completedEvaluation p A D Z T R) :=
  (completedFilteredInverse p A D Z T R C).evaluation_isIso

example : completedEvaluation p A D Z T R ≫ completedWordProjection p A D Z T R 0 0 =
    completedTensorProjection p A D Z T R 0 ≫
      DerivedCategory.Q.map (R.functor.map ((evaluationTower p A D Z T).map 0)) :=
  (completedFilteredInverse p A D Z T R C).evaluation_projections 0

example : completedEvaluation p A D Z T R ≫ completedWordProjection p A D Z T R 0 1 =
    completedTensorProjection p A D Z T R 1 ≫
      DerivedCategory.Q.map (R.functor.map ((evaluationTower p A D Z T).map 1)) :=
  (completedFilteredInverse p A D Z T R C).evaluation_projections 1

example : completedTensorProjection p A D Z T R 1 ≫
    DerivedCategory.Q.map (R.functor.map ((evaluationTower p A D Z T).map 1)) =
    completedEvaluation p A D Z T R ≫ completedWordProjection p A D Z T R 0 1 :=
  ((completedFilteredInverse p A D Z T R C).evaluation_projections 1).symm

example : C.comparison 1 ≫ completedWordProjection p A D Z T R 1 1 =
    DerivedCategory.Q.map (T.projection 1 1) ≫
      DerivedCategory.Q.map (finiteCompletionMap p A D Z T R 1 1) :=
  (completedFilteredInverse p A D Z T R C).completion_projections 1 1

example : C.comparison (-1) ≫ completedWordProjection p A D Z T R (-1) 2 =
    DerivedCategory.Q.map (T.projection (-1) 2) ≫
      DerivedCategory.Q.map (finiteCompletionMap p A D Z T R (-1) 2) :=
  (completedFilteredInverse p A D Z T R C).completion_projections (-1) 2

end MathlibExtTest.AlgebraicGeometry.CompletedFilteredPrismaticTensorsCompletedFilteredInverse
