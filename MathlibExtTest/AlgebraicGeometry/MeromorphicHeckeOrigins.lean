/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MeromorphicHeckeModels

/-!
The pole predicate entails an actual closed Cartier chart atlas. Its
completion unit retains the original E scalars, and its local Hecke
objects have the original native isomorphism-comma comparison.
-/

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates

noncomputable section

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ V : ESpace p E, GroupDescent p E G V)
  (P : PullbackPreservation p E G H)
  {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)

example (M : Modification p E G H P d U)
    (hM : MeromorphicHeckeModels.IsMeromorphic p E G H P d U M) :
    Nonempty (CartierAtlas p E d U) :=
  let ⟨A, _⟩ := hM; ⟨A⟩

/-- The pole predicate supplies integral frames of both torsors on every atlas chart, so it is
not satisfied vacuously by charts without frames. -/
example (M : Modification p E G H P d U)
    (hM : MeromorphicHeckeModels.IsMeromorphic p E G H P d U M) :
    ∃ A : CartierAtlas p E d U, ∀ i : A.index,
      Nonempty (IntegralFrame p E G H d U (A.chart i) M.left) ∧
        Nonempty (IntegralFrame p E G H d U (A.chart i) M.right) := by
  obtain ⟨A, hA⟩ := hM
  exact ⟨A, fun i ↦ let ⟨l, r, _⟩ := hA i; ⟨⟨l⟩, ⟨r⟩⟩⟩

example (Q : PoleChart p E d U) (a : E) :
    MeromorphicHeckeModels.positiveScalars p E d U Q a =
      MeromorphicHeckeModels.completionMap p E d U Q (coefficients p E Q.space a) := rfl

example (Q : PoleChart p E d U) :
    MeromorphicHeckeModels.localLeftLeg p E G d U Q ⋙
      MeromorphicHeckeModels.genericActions p E G d U Q ≅
    MeromorphicHeckeModels.localRightLeg p E G d U Q ⋙
      MeromorphicHeckeModels.genericActions p E G d U Q :=
  MeromorphicHeckeModels.localComparison p E G d U Q

#print axioms
  MathlibExt.AlgebraicGeometry.AnalyticMeromorphicCoordinates.comparisonValue
#print axioms
  MathlibExt.AlgebraicGeometry.AnalyticMeromorphicCoordinates.comparisonMatrix
#print axioms MathlibExt.AlgebraicGeometry.MeromorphicHeckeModels.leftLeg
#print axioms MathlibExt.AlgebraicGeometry.MeromorphicHeckeModels.localization
#print axioms MathlibExt.AlgebraicGeometry.MeromorphicHeckeModels.localComparison
