/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TorusBorelCoefficientModels

/-!
# Proper supported equivariant correspondence traces

The support is an actual closed scheme in X times Z and its projection
to X is proper. Every finite-approximation quotient map is fixed by
the original support projection and torsor quotient. The trace caps
the actual supported Borel--Moore class and pushes it through native
compact-support duality. Native finite-Borel comparison then transports
that computed trace. Infinite Borel spaces carry no properness or
local-compactness hypothesis here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TorusSupportedCorrespondenceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels IntegralChowChernModels
open SymplecticTorusSourceModels FiniteTorusBorelApproximationModels ComplexAnalytification
open CoefficientBettiModels CoefficientCompactSupportModels CoefficientProperDualityModels
open TorusBorelEulerModels
attribute [local instance] HasDerivedCategory.standard

variable {T : Over base} [GrpObj T] (M : TorusModel T)
  (X Z C : SchemeData) [ModObj T X.scheme] [ModObj T Z.scheme] [ModObj T C.scheme]
  (AX : AnalyticTorusAction M X.scheme) (AZ : AnalyticTorusAction M Z.scheme)
  (AC : AnalyticTorusAction M C.scheme)
  (i : C.scheme ⟶ X.scheme ⊗ Z.scheme) [IsClosedImmersion i.left]
  [IsProper (i ≫ fst X.scheme Z.scheme).left]
  (m : ℕ)
  [ModObj T (MixedTotal M X m)] [ModObj T (MixedTotal M Z m)]
  [ModObj T (MixedTotal M C m)]
  (MX : AnalyticTorusAction M (MixedTotal M X m))
  (MZ : AnalyticTorusAction M (MixedTotal M Z m))
  (MC : AnalyticTorusAction M (MixedTotal M C m))
  (PX : MixedStage M X AX m MX) (PZ : MixedStage M Z AZ m MZ)
  (PC : MixedStage M C AC m MC)

/-- The quotient maps are exactly the two actual original supported projections. -/
structure FiniteSupportedMaps where
  [closedSupport : IsClosedImmersion i.left]
  [properSupport : IsProper (i ≫ fst X.scheme Z.scheme).left]
  first : PC.quotient.quotient.scheme ⟶ PX.quotient.quotient.scheme
  second : PC.quotient.quotient.scheme ⟶ PZ.quotient.quotient.scheme
  first_normalized : PC.quotient.projection ≫ first =
    tensorHom (𝟙 (freeApproximation M.rank m)) (i ≫ fst X.scheme Z.scheme) ≫
      PX.quotient.projection
  second_normalized : PC.quotient.projection ≫ second =
    tensorHom (𝟙 (freeApproximation M.rank m)) (i ≫ snd X.scheme Z.scheme) ≫
      PZ.quotient.projection
  [proper : IsProper first.left]
  pullback : ProperPullback ℂ (spaceMap first)

/-- A trace applies the computed maps to the given actual supported homology class. -/
structure FiniteSupportedTrace extends FiniteSupportedMaps M X Z C AX AZ AC i m MX MZ MC PX PZ PC
  where
  supportDuality : DualizingComplex ℂ (space PC.quotient.quotient.scheme)
  targetDuality : DualizingComplex ℂ (space PX.quotient.quotient.scheme)
  targetDimension : ℕ
  [smooth : SmoothOfRelativeDimension targetDimension PX.quotient.quotient.scheme.hom]
  targetPurity : targetDuality.obj ≅
    (coefficientUnit ℂ (space PX.quotient.quotient.scheme))⟦(2*targetDimension : ℤ)⟧
  homologyDegree : ℤ
  cycleClass : BorelMoore ℂ (space PC.quotient.quotient.scheme) supportDuality homologyDegree

variable (D : FiniteSupportedTrace M X Z C AX AZ AC i m MX MZ MC PX PZ PC)

/-- Its degree is the actual target real dimension minus the actual supported homology degree. -/
def traceShift : ℤ := (2*D.targetDimension : ℤ)-D.homologyDegree

/-- The operator is precisely native cap, proper push and inverse finite Borel comparison. -/
def trace (n : ℤ) (sourceRange : n < 2*m+1)
    (targetRange : n+traceShift M X Z C AX AZ AC i m MX MZ MC PX PZ PC D < 2*m+1) :
    letI := AX.action
    letI := AX.continuous
    letI := AZ.action
    letI := AZ.continuous
    BorelCohomologyModels.H (Fin M.rank → ℂˣ) (space Z.scheme) n →ₗ[ℂ]
      BorelCohomologyModels.H (Fin M.rank → ℂˣ) (space X.scheme)
        (n+traceShift M X Z C AX AZ AC i m MX MZ MC PX PZ PC D) := by
  letI := AX.action
  letI := AX.continuous
  letI := AZ.action
  letI := AZ.continuous
  exact (MixedStage.comparison M X AX m MX PX
    (n+traceShift M X Z C AX AZ AC i m MX MZ MC PX PZ PC D) targetRange).symm.toLinearMap ∘ₗ
    cohomologyCast (show (2*D.targetDimension : ℤ)-(D.homologyDegree-n) =
      n+traceShift M X Z C AX AZ AC i m MX MZ MC PX PZ PC D by unfold traceShift; omega) ∘ₗ
    supportedTrace ℂ (spaceMap D.first) (spaceMap D.second) D.pullback D.supportDuality
      D.targetDuality D.targetDimension D.targetPurity D.homologyDegree n D.cycleClass ∘ₗ
    (MixedStage.comparison M Z AZ m MZ PZ n sourceRange).toLinearMap

end MathlibExt.AlgebraicGeometry.TorusSupportedCorrespondenceModels
