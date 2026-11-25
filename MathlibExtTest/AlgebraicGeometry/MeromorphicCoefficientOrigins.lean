/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.FramedMeromorphicGroupModels

/-! The completed map has actual finite-pole coefficients as its domain.
The image-subring dictionary and every original representation matrix
use the same original restriction/completion maps.
-/

open CategoryTheory Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicCoefficientCompletion
open FramedMeromorphicGroupModels AlgebraicGroupPointRepresentations

noncomputable section

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ V : ESpace p E, GroupDescent p E G V)
  (P : PullbackPreservation p E G H)
  {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
  (Q : PoleChart p E d U)
  (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))

example (a : E) : completedMap p E d U Q (meromorphicScalars p E d U Q a) =
    MeromorphicHeckeModels.genericScalars p E d U Q a :=
  completedMap_scalars p E d U Q a

example (hi : Function.Injective (puncturedMap p E d U Q h))
    (a : MeromorphicRing p E d U Q) :
    imageCompletion p E d U Q h hi ((puncturedMap p E d U Q h).rangeRestrict a) =
      completedMap p E d U Q a := imageCompletion_normalized p E d U Q h hi a

example (M : Modification p E G H P d U)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right)
    (F : GroupFactorization p E G H P d U Q h M left right)
    (n : ℕ) (ρ : Representation E G n) (i j : Fin n) :
    completedMatrix p E G H P d U Q h M left right F n ρ i j =
      completedMap p E d U Q
        (meromorphicMatrix p E G H P d U Q h M left right F n ρ i j) :=
  completedMatrix_entries p E G H P d U Q h M left right F n ρ i j

#print axioms
  MathlibExt.AlgebraicGeometry.MeromorphicCoefficientCompletion.sectionMap_coefficients
#print axioms MathlibExt.AlgebraicGeometry.MeromorphicCoefficientCompletion.completedMap
#print axioms MathlibExt.AlgebraicGeometry.MeromorphicCoefficientCompletion.imageCompletion
#print axioms
  MathlibExt.AlgebraicGeometry.MeromorphicCoefficientCompletion.imageCompletion_normalized
#print axioms MathlibExt.AlgebraicGeometry.FramedMeromorphicGroupModels.completedElement
#print axioms MathlibExt.AlgebraicGeometry.FramedMeromorphicGroupModels.completedMatrix_entries
