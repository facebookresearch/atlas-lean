/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MeromorphicGroupFactorizationMeromorphicGroupFactorizationUnique

/-!
Point-level uniqueness of the finite-pole factorization gives
structure-level uniqueness: the factorizations form a subsingleton.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicGeometry.MeromorphicGroupFactorizationMeromorphicGroupFactorizationUnique

open _root_.CategoryTheory Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicCoefficientCompletion
open FramedMeromorphicGroupModels
open WantedExt.AlgebraicGeometry.MeromorphicGroupFactorization

/-- Any two finite-pole factorizations of the same framed modification agree as structures. -/
theorem subsingleton_groupFactorization
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E)) G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U)
    (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
    (hi : Function.Injective (puncturedMap p E d U Q h))
    (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right) :
    Subsingleton (GroupFactorization p E G H P d U Q h M left right) := by
  constructor
  intro F N
  obtain ⟨eF, hF⟩ := F
  obtain ⟨eN, hN⟩ := N
  have hEq : eF = eN :=
    meromorphicGroupFactorization_unique p E G H P d U Q h hi M left right
      ⟨eF, hF⟩ ⟨eN, hN⟩
  subst hEq
  rfl

end MathlibExtTest.AlgebraicGeometry.MeromorphicGroupFactorizationMeromorphicGroupFactorizationUnique
