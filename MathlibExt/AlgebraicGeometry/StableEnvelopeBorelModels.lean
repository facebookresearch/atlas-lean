/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StableEnvelopeNormalModels

/-!
# Native fixed-component Borel restriction and signed normal Euler classes

Every component action is the original ambient torus action. The
negative bundle is the computed chamber eigensum, with its actual
inclusion into the pulled ambient tangent. Its Euler class is the
native zero-section finite-Borel class relative to the coefficient system's
orientation datum (the same datum orients the coordinate classes). The
leading-character equation ties its leading term to the coefficient
characters; polarization then supplies its sign. For the complex
orientation these are the usual equivariant Euler classes; for another
datum each is a unit multiple of the usual one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.StableEnvelopeBorelModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels TorusDifferentialGeometryModels
open TorusPolynomialDegreeModels IntegralChowChernModels SymplecticTorusSourceModels
open TorusFixedSchemeModels LinearizedLineBundles ComplexAnalytification
open TorusBorelEulerModels TorusBorelCoefficientModels ResidualTorusDegreeModels
open FiniteTorusBorelApproximationModels StableEnvelopeNormalModels
open scoped DirectSum

variable {A T : Over base} [GrpObj A] [GrpObj T]
  (MA : TorusModel A) (MT : TorusModel T) (S : Subtorus A T) (P : TorusSplitting S)
  (X : Over base) [ModObj A X] [ModObj T X] (TX : TorusTangentActionData MT X)
  (AX : AnalyticTorusAction MT X)
  (F : SchemeData) (i : F.scheme ⟶ X) (hi : FixedPoint A X i)
  (N : NormalGeometry MA i hi) (R : NormalRoots N)
  (C : Chamber R.roots) (L : ChamberCocharacter C) (Coefficients : CoefficientCoordinates MT)

/-- All cohomology and bundle operations are bound to the same original component geometry. -/
structure ComponentBorelData where
  [action : ModObj T F.scheme]
  analytic : AnalyticTorusAction MT F.scheme
  equivariant : γ[T,F.scheme] ≫ i = (T ◁ i) ≫ γ[T,X]
  topology : letI := AX.action
    letI := AX.continuous
    letI := analytic.action
    letI := analytic.continuous
    ∀ (g : Fin MT.rank → ℂˣ) (z : space F.scheme),
      spaceMap i (g • z) = g • spaceMap i z
  polynomial : PolynomialAction MT Coefficients F.scheme analytic
  residual : ResidualGeometry MA MT S P F analytic
  first : TorusMorphismCoordinates MT MA (firstProjection P)
  restricted : Linearization T F.scheme ((Scheme.Modules.pullback i.left).obj (Tangent X))
  restriction : restricted.comparison.hom = pulledLinearComparison i equivariant TX.linearization
  negative : Linearization T F.scheme (negativeNormal R C L)
  negative_transport : IsLinearizedMap negative restricted (negativeInclusion R C L)
  m : ℕ
  [stageAction : ModObj T (MixedTotal MT F m)]
  stageAnalytic : AnalyticTorusAction MT (MixedTotal MT F m)
  stage : MixedStage MT F analytic m stageAnalytic
  euler : EquivariantEulerGeometry MT F analytic m stageAnalytic stage negative
    Coefficients.orientation (negativeRank R C L)
  leading :
    let a := homogeneous MT F.scheme analytic (2*negativeRank R C L)
      (EquivariantEulerGeometry.euler MT F analytic m stageAnalytic stage negative euler)
    let b := polynomial.action (first.polynomialMap (negativeEuler R C L))
      (gradedUnit MT F.scheme analytic)
    (negativeRank R C L = 0 ∧ a = gradedUnit MT F.scheme analytic) ∨
      (0 < negativeRank R C L ∧ a-b ∈
        degreeFiltration residual Coefficients polynomial (negativeRank R C L-1))

variable (B : ComponentBorelData MA MT S P X TX AX F i hi N R C L Coefficients)

abbrev ComponentH :=
  letI := B.action
  H MT F.scheme B.analytic

/-- The restriction is the native Borel pullback of the actual closed component map. -/
def ambientRestriction :
    H MT X AX →ₗ[ℂ] ComponentH MA MT S P X TX AX F i hi N R C L Coefficients B := by
  letI := AX.action
  letI := AX.continuous
  letI := B.action
  letI := B.analytic.action
  letI := B.analytic.continuous
  exact BorelCohomologyModels.gradedRestriction (spaceMap i) B.topology

/-- This is the Euler class of the actual negative normal bundle, relative to the coefficient
system's orientation datum. -/
def negativeClass : ComponentH MA MT S P X TX AX F i hi N R C L Coefficients B := by
  letI := B.action
  letI := B.analytic.action
  letI := B.analytic.continuous
  letI := B.stageAction
  exact homogeneous MT F.scheme B.analytic (2*negativeRank R C L)
    (EquivariantEulerGeometry.euler MT F B.analytic B.m B.stageAnalytic B.stage B.negative B.euler)

/-- Cup by that Euler class uses the actual Yoneda product in every degree. -/
def negativeEulerCup : Module.End ℂ
    (ComponentH MA MT S P X TX AX F i hi N R C L Coefficients B) := by
  letI := B.action
  letI := B.analytic.action
  letI := B.analytic.continuous
  letI := B.stageAction
  let e := EquivariantEulerGeometry.euler MT F B.analytic B.m B.stageAnalytic B.stage B.negative
    B.euler
  exact DirectSum.toModule ℂ ℤ (H MT F.scheme B.analytic) (fun n =>
    (homogeneous MT F.scheme B.analytic (2*negativeRank R C L+n)).comp
      (CoefficientBettiModels.cupBilinear ℂ
        (MathlibExt.Topology.ContinuousBorel.borel (Fin MT.rank → ℂˣ) (space F.scheme))
        (2*negativeRank R C L) n e))

/-- The sign is fixed by the chosen source square-root polarization. -/
def signedEulerCup (e : Polarization R C L) : Module.End ℂ
    (ComponentH MA MT S P X TX AX F i hi N R C L Coefficients B) :=
  (e.sign : ℤ) • negativeEulerCup MA MT S P X TX AX F i hi N R C L Coefficients B

end MathlibExt.AlgebraicGeometry.StableEnvelopeBorelModels
