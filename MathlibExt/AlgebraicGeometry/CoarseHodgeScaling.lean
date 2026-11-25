/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FixedParameterLambdaModuli

/-!
# Actual coarse scaling and nonzero Hodge fibres

Scaling descends through the actual universal Hodge quotient. Its native
group action is constrained by the literal quotient-equivariance and affine
parameter multiplication diagrams. A constant scaling is the actual native
GL1 point corresponding to a unit in the structure sheaf.

For lambda nonzero, the comparison to the lambda-one fibre is the actual
scaling by lambda inverse; its inverse scales by lambda. Both equalities are
normalized after the native fibre inclusions, so the comparison is not an
independently selected fibre isomorphism.

Source: Simpson, alg-geom/9604005v1, section 4 after Proposition 4.1.
Source group/frame/pullback/fibre primitives retain their imported native
Mathlib/Stacks author, revision, license and adaptation notices.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoarseHodgeScaling

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open RelativeFramedLambdaFamilies RelativeLambdaPullbackSystems AdmissibleRelativeLambdaFamilies
open FramedLambdaFamilyFunctor HodgeModuliSchemes FixedParameterLambdaModuli
  GeneralLinearFrameSchemes
open ProjectiveLineSystems

variable [FrameTheory 1] [ScalingParameterTheory]

def constantScalar (a : ℂˣ) : scalarBase ⟶ frameScheme 1 :=
  (ScalingParameterTheory.units scalarBase).symm
    (Units.map (CoherentCurveLinearSeries.globalScalarMap scalarBase.hom) a)

variable (X : ComplexScheme) (x : scalarBase ⟶ X) (n : ℕ) (P : PullbackSystem X x n)
  (V : UnitFibreComparison X x n P) (d : ℕ) (H : LineBundle X.left)
  (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
  (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
    (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
  (T : BettiCharacteristicClasses.ProjectiveBundleTheory D Q)
  [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
  (F : FibreTests X x n P V d H)
  (RP : ReindexingProofs X x n P V d H D Q T F)
  (AP : ActionAdmissibility X x n P V d H D Q T F) [FrameTheory n]
  (R : HodgeRepresentation X x n P V d H D Q T F RP AP)
  (C : HodgeQuotient X x n P V d H D Q T F RP AP R)

structure ScalingDescent where
  [action : ModObj (frameScheme 1) C.scheme]
  quotient : letI := R.scalingAction;
    γ[frameScheme 1,R.scheme] ≫ C.quotient =
      (frameScheme 1 ◁ C.quotient) ≫ γ[frameScheme 1,C.scheme]
  parameter : γ[frameScheme 1,C.scheme] ≫ C.parameter =
    (frameScheme 1 ◁ C.parameter) ≫ γ[frameScheme 1,parameterLine]

def scaleMap (S : ScalingDescent X x n P V d H D Q T F RP AP R C) (a : ℂˣ) : C.scheme ⟶
  C.scheme := by
  letI := S.action
  exact CartesianMonoidalCategory.lift (toUnit C.scheme ≫ constantScalar a) (𝟙 C.scheme) ≫
    γ[frameScheme 1,C.scheme]

structure NonzeroFibreScaling (S : ScalingDescent X x n P V d H D Q T F RP AP R C)
    (lambda : ℂ) (nonzero : lambda ≠ 0) where
  iso : fibre C.scheme C.parameter (complexParameterPoint lambda) ≅
    fibre C.scheme C.parameter (complexParameterPoint 1)
  forward : iso.hom ≫ fibreInclusion C.scheme C.parameter (complexParameterPoint 1) =
    fibreInclusion C.scheme C.parameter (complexParameterPoint lambda) ≫
      scaleMap X x n P V d H D Q T F RP AP R C S (Units.mk0 lambda nonzero)⁻¹
  inverse : iso.inv ≫ fibreInclusion C.scheme C.parameter (complexParameterPoint lambda) =
    fibreInclusion C.scheme C.parameter (complexParameterPoint 1) ≫
      scaleMap X x n P V d H D Q T F RP AP R C S (Units.mk0 lambda nonzero)

end MathlibExt.AlgebraicGeometry.CoarseHodgeScaling
