/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ReducedPicardTensorActions
public import MathlibExt.AlgebraicGeometry.CurveCohomologyDeterminantModels

/-!
# The actual reduced-curve Poincare family and beta map

The raw family is D(I tensor M)^-1 tensor D(M) tensor D(I), on the actual
product of the compactified Jacobian and connected Picard-zero group.
Every determinant is fixed by the actual derived curve-cohomology object
and all affine presentation/base-change normalizations.

Rigidification uses the inverse of its actual restriction at an arbitrary
q-stable point. The restriction at O_C remains the constant D(O_C) line;
no basis of that coefficient line is silently selected. The beta map is
then the native Picard universal parameter map of this rigidified family.
Neither an O_C point of the compactification nor autoduality is assumed.
Source: MRV arXiv:1207.7233v5, Section 5, Equations (5.1)--(5.4), pp18--19.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ReducedPoincareFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CoherentCurveLinearSeries AlgebraicLineBundleFamilies PointedPicardFamilies
open NumericalCompactifiedJacobians ReducedPicardTensorActions
open FourierMukai PositiveCurveDeterminants CurveCohomologyDeterminantModels
open SchemeDeterminantPresentations AffineDerivedCoefficientModules NativeLineDuals
open SheafTensorSections NativeTensorComparisons

attribute [local instance] HasDerivedCategory.standard FineCompactifiedJacobian.proper

variable {k : Type} [Field k] [IsAlgClosed k]
  [HasDerivedPullbacks.{0}] [HasDerivedScalarExtensions.{0}] [HasDerivedPushforwards.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  (S : AffineSources) (A : DeterminantSystem S)
  (C : Over (Spec (.of k))) [IsProperCurve C.hom] [TorsionFreeRestrictions C.left]
  (q : Polarization C.left) (s : SmoothMarking C)
  (M : FineCompactifiedJacobian C q s) (J : PicardZeroModel C s.p)

abbrev parameterBase := prod M.J J.J

def universalSheaf : (prod C (parameterBase C q s M J)).left.Modules :=
  familyPullback C M.J (parameterBase C q s M J) M.F prod.fst

def universalLine : (prod C (parameterBase C q s M J)).left.Modules :=
  familyPullback C J.J (parameterBase C q s M J) J.P prod.snd

def universalTensor : (prod C (parameterBase C q s M J)).left.Modules :=
  moduleTensor (prod C (parameterBase C q s M J)).left
    (universalSheaf C q s M J) (universalLine C q s M J)

def curveProjection : (prod C (parameterBase C q s M J)).left ⟶ (parameterBase C q s M J).left :=
  (prod.snd : prod C (parameterBase C q s M J) ⟶ parameterBase C q s M J).left

structure PoincareCohomologyData where
  tensorPerfect : IsPerfectTwoTermOn
    ((cohomologyObject (curveProjection C q s M J) (universalTensor C q s M J))⟦(1 : ℤ)⟧)
  linePerfect : IsPerfectTwoTermOn
    ((cohomologyObject (curveProjection C q s M J) (universalLine C q s M J))⟦(1 : ℤ)⟧)
  sheafPerfect : IsPerfectTwoTermOn
    ((cohomologyObject (curveProjection C q s M J) (universalSheaf C q s M J))⟦(1 : ℤ)⟧)
  unitPerfect : IsPerfectTwoTermOn ((cohomologyObject C.hom (structureModule C.left))⟦(1 : ℤ)⟧)

variable (D : PoincareCohomologyData C q s M J)

def rawPoincareModule : (parameterBase C q s M J).left.Modules :=
  moduleTensor (parameterBase C q s M J).left
    (dualModule (parameterBase C q s M J).left
      (determinantOfCohomology A (curveProjection C q s M J)
        (universalTensor C q s M J) D.tensorPerfect).line)
    (moduleTensor (parameterBase C q s M J).left
      (determinantOfCohomology A (curveProjection C q s M J)
        (universalLine C q s M J) D.linePerfect).line
      (determinantOfCohomology A (curveProjection C q s M J)
        (universalSheaf C q s M J) D.sheafPerfect).line)

def coefficientDeterminant : (Spec (.of k)).Modules :=
  (determinantOfCohomology A C.hom (structureModule C.left) D.unitPerfect).line

def identityPoint : 𝟙_ (Over (Spec (.of k))) ⟶ J.J := by
  letI := J.group
  exact η[J.J]

def rigidifyingModule (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ M.J) : J.J.left.Modules :=
  (Scheme.Modules.pullback (sectionAt M.J J.J p0).left).obj (rawPoincareModule S A C q s M J D)

def rigidifiedModule (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ M.J) :
    (parameterBase C q s M J).left.Modules :=
  moduleTensor (parameterBase C q s M J).left (rawPoincareModule S A C q s M J D)
    ((Scheme.Modules.pullback (prod.snd : parameterBase C q s M J ⟶ J.J).left).obj
      (dualModule J.J.left (rigidifyingModule S A C q s M J D p0)))

/-- The geometric properties needed to apply the existing Picard universal
property. No beta-isomorphism or inverse-kernel identity is a field. -/
structure PoincareFamilyData (p0 : 𝟙_ (Over (Spec (.of k))) ⟶ M.J) where
  target : PicardZeroModel M.J p0
  rawLine : IsLineBundle (rawPoincareModule S A C q s M J D)
  pointLine : IsLineBundle (rigidifyingModule S A C q s M J D p0)
  pointTensor : TensorPullbackComparison (sectionAt M.J J.J p0).left
  rigidifiedLine : IsLineBundle (rigidifiedModule S A C q s M J D p0)
  algebraicallyTrivial : IsFibrewiseAlgebraicallyTrivial
    (prod.snd : parameterBase C q s M J ⟶ J.J).left (rigidifiedModule S A C q s M J D p0)
  identityCoefficient :
    (Scheme.Modules.pullback (pointSection M.J J.J (identityPoint C s J)).left).obj
      (rawPoincareModule S A C q s M J D) ≅
        (Scheme.Modules.pullback M.J.hom).obj (coefficientDeterminant S A C q s M J D)

variable {p0 : 𝟙_ (Over (Spec (.of k))) ⟶ M.J}
  (P : PoincareFamilyData S A C q s M J D p0)

/-- Canonical normalization uses evaluation on the actual point restriction. -/
def rigidificationIso :
    (Scheme.Modules.pullback (sectionAt M.J J.J p0).left).obj
      (rigidifiedModule S A C q s M J D p0) ≅ structureModule J.J.left := by
  let H := rigidifyingModule S A C q s M J D p0
  let E := A.duality J.J.left H P.pointLine
  letI := E.invertible
  let pullDual :
      (Scheme.Modules.pullback (sectionAt M.J J.J p0).left).obj
        ((Scheme.Modules.pullback (prod.snd : parameterBase C q s M J ⟶ J.J).left).obj
          (dualModule J.J.left H)) ≅ dualModule J.J.left H :=
    (Scheme.Modules.pullbackComp (sectionAt M.J J.J p0).left
      (prod.snd : parameterBase C q s M J ⟶ J.J).left).app (dualModule J.J.left H) ≪≫
    (Scheme.Modules.pullbackCongr (by
      rw [← Over.comp_left]
      exact congrArg Over.Hom.left (prod.lift_snd _ _))).app (dualModule J.J.left H) ≪≫
    (Scheme.Modules.pullbackId J.J.left).app (dualModule J.J.left H)
  exact (P.pointTensor.iso (rawPoincareModule S A C q s M J D)
      ((Scheme.Modules.pullback (prod.snd : parameterBase C q s M J ⟶ J.J).left).obj
        (dualModule J.J.left H))) ≪≫
    NativeTensorComparisons.tensorIso (Iso.refl H) pullDual ≪≫
    NativeTensorComparisons.tensorIso (Iso.refl H) (eqToIso E.object_eq.symm) ≪≫
    asIso E.evaluation.evaluation

def beta : J.J ⟶ P.target.J :=
  (P.target.universal J.J (rigidifiedModule S A C q s M J D p0) P.rigidifiedLine
    ⟨rigidificationIso S A C q s M J D P⟩ P.algebraicallyTrivial).choose

def betaFamilyIso :
    familyPullback M.J P.target.J J.J P.target.P (beta S A C q s M J D P) ≅
      rigidifiedModule S A C q s M J D p0 :=
  Classical.choice (P.target.universal J.J (rigidifiedModule S A C q s M J D p0) P.rigidifiedLine
    ⟨rigidificationIso S A C q s M J D P⟩ P.algebraicallyTrivial).choose_spec.1

/-- Group compatibility for the actual Picard-universal beta parameter map. -/
structure BetaGroupCompatibility : Prop where
  unit : letI := J.group; letI := P.target.group;
    identityPoint C s J ≫ beta S A C q s M J D P = η[P.target.J]
  multiply : letI := J.group; letI := P.target.group;
    μ[J.J] ≫ beta S A C q s M J D P =
      tensorHom (beta S A C q s M J D P) (beta S A C q s M J D P) ≫ μ[P.target.J]

end MathlibExt.AlgebraicGeometry.ReducedPoincareFamilies
