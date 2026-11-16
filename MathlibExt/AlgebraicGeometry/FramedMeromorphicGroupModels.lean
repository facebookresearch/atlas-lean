/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MeromorphicCoefficientCompletion

/-!
# Actual G-valued meromorphic coefficients and their formal completion

A factorization is a genuine G-point over the original A[1/t], whose
restriction equals the original punctured torsor isomorphism in its
original integral frames. Its formal value is then computed by the
actual E-algebra completion map. Every representation matrix is obtained
from that same G-point and the original representation functor.

Factorization existence uses affine finite-presentation reductive G
geometry and is requested separately. Unframed torsor algebraization,
all refinement/coherence and period-position comparisons remain separate
operations. The source comparison has not been replaced by a freely
chosen element of G of a completed ring.

Reference: Fargues--Scholze, arXiv:2102.13459v4, Section III.3 and VI.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FramedMeromorphicGroupModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicCoefficientCompletion
open AlgebraicGroupPointRepresentations

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ V : ESpace p E, GroupDescent p E G V)
  (P : PullbackPreservation p E G H)
  {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
  (Q : PoleChart p E d U)
  (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
  (M : Modification p E G H P d U)
  (left : IntegralFrame p E G H d U Q M.left)
  (right : IntegralFrame p E G H d U Q M.right)

/-- The original punctured G-point factors through actual finite-pole coefficients. -/
structure GroupFactorization where
  element : (groups E G).obj (meromorphicTest p E d U Q)
  normalized : ((groups E G).map (punctureTestMap p E d U Q h)).hom element =
    comparisonElement p E G H P d U Q M left right

variable (F : GroupFactorization p E G H P d U Q h M left right)

/-- The completed G-point is the original factorized point mapped by actual completion. -/
def completedElement : (groups E G).obj (completedTest p E d U Q) :=
  ((groups E G).map (completionTestMap p E d U Q)).hom F.element

/-- The actual original representation matrix over the finite-pole ring. -/
def meromorphicMatrix (n : ℕ) (ρ : Representation E G n) :
    Matrix (Fin n) (Fin n) (MeromorphicRing p E d U Q) :=
  actionMatrix E G n ρ (meromorphicTest p E d U Q) F.element

/-- The formal representation matrix uses that same completed G-point. -/
def completedMatrix (n : ℕ) (ρ : Representation E G n) :
    Matrix (Fin n) (Fin n) (MeromorphicHeckeModels.GenericRing p E d U Q) :=
  actionMatrix E G n ρ (completedTest p E d U Q)
    (completedElement p E G H P d U Q h M left right F)

omit [Fact p.Prime] in
/-- Every original matrix entry is completed by the actual finite-pole coefficient map. -/
theorem completedMatrix_entries (n : ℕ) (ρ : Representation E G n) (i j : Fin n) :
    completedMatrix p E G H P d U Q h M left right F n ρ i j =
      completedMap p E d U Q
        (meromorphicMatrix p E G H P d U Q h M left right F n ρ i j) := by
  have hn := ConcreteCategory.congr_hom
    (ρ.naturality (completionTestMap p E d U Q)) F.element
  exact congrArg (fun a : GL (Fin n) (MeromorphicHeckeModels.GenericRing p E d U Q) ↦
    (a : Matrix (Fin n) (Fin n) (MeromorphicHeckeModels.GenericRing p E d U Q)) i j) hn

end MathlibExt.AlgebraicGeometry.FramedMeromorphicGroupModels
