/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.MeromorphicHeckeCoordinates

@[expose] public section

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.MeromorphicHeckeCoordinates

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates
open WantedExt.AlgebraicGeometry.MeromorphicHeckeCoordinates

/-- The comparison value is equivariant for right multiplication. -/
theorem comparisonValue_mul_of_normalization
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U) (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right)
    (T : Site p E Q.puncture.space)
    (a b : (pointGroups p E G).obj (op T.left)) :
    comparisonValue p E G H P d U Q M left right T (a * b)
      = comparisonValue p E G H P d U Q M left right T a * b := by
  have h1 := comparison_refinement_normalization p E G H P
    d U Q M left right T (a * b)
  have h2 := comparison_refinement_normalization p E G H P
    d U Q M left right T a
  rw [h1, h2]
  exact (mul_assoc (((pointGroups p E G).map T.hom.op).hom
    (comparisonElement p E G H P d U Q M left right)) a b).symm

end MathlibExtTest.AlgebraicGeometry.MeromorphicHeckeCoordinates
