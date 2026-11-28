/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SymplecticTorusSourceModels
public import MathlibExt.AlgebraicGeometry.TorusPolynomialDegreeModels

/-!
# Actual finite free approximations and their native Borel comparisons

U_m is the actual open in C^(r(m+1)) where each coordinate block is
nonzero. Its action is fixed on every original polynomial coordinate.
The mixed total space is the literal product U_m times X and its quotient
is characterized by an actual fppf torus torsor. Cohomology comparison
uses the native Borel quotient augmentation and product projection.
No finite-dimensional or local-compactness assumption is made on Borel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteTorusBorelApproximationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels TorusPolynomialDegreeModels
open SymplecticTorusSourceModels IntegralChowChernModels GroupTorsorGeometry ComplexAnalytification
open CoefficientBettiModels MathlibExt.Topology.ContinuousBorel
attribute [local instance] HasDerivedCategory.standard

abbrev ApproximationRing (r m : ℕ) := MvPolynomial (Fin r × Fin (m+1)) ℂ

def affineSpace (r m : ℕ) : Over base :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ (ApproximationRing r m))))

def affineCoordinate (r m : ℕ) (i : Fin r) (j : Fin (m + 1)) : Γ((affineSpace r m).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (ApproximationRing r m))).inv.hom (MvPolynomial.X (i,j))

/-- The actual open product of punctured coordinate blocks. -/
def approximationOpen (r m : ℕ) : (affineSpace r m).left.Opens :=
  ⨅ i : Fin r, ⨆ j : Fin (m+1), (affineSpace r m).left.basicOpen (affineCoordinate r m i j)

def freeApproximation (r m : ℕ) : Over base :=
  Over.mk ((approximationOpen r m).ι ≫ (affineSpace r m).hom)

def freeCoordinate (r m : ℕ) (i : Fin r) (j : Fin (m + 1)) : Γ((freeApproximation r m).left, ⊤) :=
  (approximationOpen r m).ι.appTop (affineCoordinate r m i j)

/-- This quotient is characterized by the same actual torsor total space and action. -/
structure QuotientScheme {T Y : Over base} [GrpObj T] [ModObj T Y] where
  quotient : SchemeData
  torsor : Torsor T quotient.scheme
  total : Y ≅ torsor.total
  equivariant : γ[T,Y] ≫ total.hom = (T ◁ total.hom) ≫ torsor.action.smul

def QuotientScheme.projection {T Y : Over base} [GrpObj T] [ModObj T Y] (Q : QuotientScheme (T := T)
  (Y := Y)) :
    Y ⟶ Q.quotient.scheme := Q.total.hom ≫ Q.torsor.projection

theorem QuotientScheme.invariant {T Y : Over base} [GrpObj T] [ModObj T Y]
    (Q : QuotientScheme (T := T) (Y := Y)) : γ[T,Y] ≫ Q.projection = snd T Y ≫ Q.projection := by
  dsimp only [projection]
  rw [← Category.assoc, Q.equivariant, Category.assoc, Q.torsor.invariant]
  rw [← Category.assoc, whiskerLeft_snd, Category.assoc]

def quotientAugmentation {T Y : Over base} [GrpObj T] [ModObj T Y]
    (M : TorusModel T) (A : AnalyticTorusAction M Y) (Q : QuotientScheme (T := T) (Y := Y))
    (h : letI := A.action; ∀ (g : Fin M.rank → ℂˣ) (y : space Y),
      spaceMap Q.projection (g • y) = spaceMap Q.projection y) :
    letI := A.action
    letI := A.continuous
    borel (Fin M.rank → ℂˣ) (space Y) ⟶ space Q.quotient.scheme := by
  letI := A.action
  letI := A.continuous
  exact borelToQuotient (spaceMap Q.projection) h

variable {T : Over base} [GrpObj T] (M : TorusModel T) (X : SchemeData) [ModObj T X.scheme]
  (AX : AnalyticTorusAction M X.scheme) (m : ℕ)

abbrev MixedTotal := freeApproximation M.rank m ⊗ X.scheme

/-- The diagonal action is fixed by the actual coordinate action and original X projection. -/
structure MixedStage [ModObj T (MixedTotal M X m)]
    (A : AnalyticTorusAction M (MixedTotal M X m)) where
  coordinate : ∀ (i : Fin M.rank) (j : Fin (m+1)),
    γ[T,MixedTotal M X m].left.appTop
      ((fst (freeApproximation M.rank m) X.scheme).left.appTop (freeCoordinate M.rank m i j)) =
    (fst T (MixedTotal M X m)).left.appTop (coordinateUnit M i : Γ(T.left, ⊤)) *
      (snd T (MixedTotal M X m)).left.appTop
        ((fst (freeApproximation M.rank m) X.scheme).left.appTop (freeCoordinate M.rank m i j))
  projection : γ[T,MixedTotal M X m] ≫ snd (freeApproximation M.rank m) X.scheme =
    (T ◁ snd (freeApproximation M.rank m) X.scheme) ≫ γ[T,X.scheme]
  quotient : QuotientScheme (T := T) (Y := MixedTotal M X m)
  invariant : letI := A.action
    ∀ (g : Fin M.rank → ℂˣ) (y : space (MixedTotal M X m)),
      spaceMap quotient.projection (g • y) = spaceMap quotient.projection y
  topProjection : letI := A.action
    letI := AX.action
    ∀ (g : Fin M.rank → ℂˣ) (y : space (MixedTotal M X m)),
      spaceMap (snd (freeApproximation M.rank m) X.scheme) (g • y) =
        g • spaceMap (snd (freeApproximation M.rank m) X.scheme) y
  augmentation : ∀ n : ℤ, Function.Bijective
    (cohomologyPullback ℂ (quotientAugmentation M A quotient invariant) n)
  approximation : letI := AX.action
    letI := AX.continuous
    letI := A.action
    letI := A.continuous
    ∀ (n : ℤ), n < 2*m+1 → Function.Bijective
      (cohomologyPullback ℂ
        (borelMap (spaceMap (snd (freeApproximation M.rank m) X.scheme)) topProjection) n)

variable [ModObj T (MixedTotal M X m)] (A : AnalyticTorusAction M (MixedTotal M X m))
  (P : MixedStage M X AX m A)

/-- Comparison is the inverse native torsor augmentation after native Borel projection. -/
def MixedStage.comparison (n : ℤ) (hn : n < 2 * m + 1) :
    letI := AX.action
    letI := AX.continuous
    BorelCohomologyModels.H (Fin M.rank → ℂˣ) (space X.scheme) n ≃ₗ[ℂ]
      Cohomology ℂ (space P.quotient.quotient.scheme) n := by
  letI := AX.action
  letI := AX.continuous
  letI := A.action
  letI := A.continuous
  exact (LinearEquiv.ofBijective
    (cohomologyPullback ℂ
      (borelMap (spaceMap (snd (freeApproximation M.rank m) X.scheme)) P.topProjection) n)
    (P.approximation n hn)).trans
      (LinearEquiv.ofBijective
        (cohomologyPullback ℂ (quotientAugmentation M A P.quotient P.invariant) n)
        (P.augmentation n)).symm

/-- The diagonal action, analytification and quotient stage are chosen as one native source. -/
structure MixedApproximationSource {T : Over base} [GrpObj T] (M : TorusModel T)
    (X : SchemeData) [ModObj T X.scheme] (AX : AnalyticTorusAction M X.scheme) (m : ℕ) where
  [action : ModObj T (MixedTotal M X m)]
  analytic : AnalyticTorusAction M (MixedTotal M X m)
  stage : MixedStage M X AX m analytic

end MathlibExt.AlgebraicGeometry.FiniteTorusBorelApproximationModels
