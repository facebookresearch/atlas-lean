/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicEquivariantCoefficientModels
public import MathlibExt.Algebra.Module.EndScalarRestriction

/-!
# Actual projective fixed-locus pushes and coefficient localization

The graded map is assembled from the native projective Kresch pushes.
Polynomial linearity is a proof property of that same map. The localized
map is its native tensor extension, with no independently supplied push.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EquivariantProjectivePushModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open AlgebraicWeightBundleModels AlgebraicEquivariantChowModels
  AlgebraicEquivariantCoefficientModels
open EquivariantCharacterLineModels StackChowGroups StackCycleRelations
open scoped DirectSum TensorProduct

variable (D : CycleConstructionData base (FiniteTypeArtin ℂ)) (K : KreschPresentation D)
  {F X : Over base} [ModObj Gm F] [ModObj Gm X]
  (Q : EquivariantSource F) (R : EquivariantSource X) (i : F ⟶ X)
  (hi : γ[Gm,F] ≫ i = (Gm ◁ i) ≫ γ[Gm,X]) (M : EquivariantMap Q R i hi)
  (P : ProjectiveChowPushData D K Q.inScope R.inScope M.map)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Each graded component is the actual projective quotient-stack push. -/
def gradedPush : GradedChow Q D K →ₗ[ℚ] GradedChow R D K :=
  DirectSum.toModule ℚ ℤ (GradedChow R D K) (fun d =>
    (DirectSum.lof ℚ ℤ (EquivariantChow D K R) d).comp (equivariantProjectivePush D K P d))

variable (CQ : CharacterChernData Q D K characterOne) (CR : CharacterChernData R D K characterOne)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Compatibility tests the prescribed character polynomial action on the native push. -/
def PolynomialCompatible : Prop :=
  ∀ (p : Polynomial ℚ) (a : GradedChow Q D K),
    gradedPush D K Q R i hi M P (polynomialAction Q D K CQ p a) =
      polynomialAction R D K CR p (gradedPush D K Q R i hi M P a)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The polynomial-linear map is the same native graded push. -/
def polynomialPush (h : PolynomialCompatible D K Q R i hi M P CQ CR) :
    letI := polynomialModule Q D K CQ
    letI := polynomialModule R D K CR
    GradedChow Q D K →ₗ[Polynomial ℚ] GradedChow R D K :=
  MathlibExt.EndScalarRestriction.intertwiningMap
    (polynomialAction Q D K CQ) (polynomialAction R D K CR) (gradedPush D K Q R i hi M P) h

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Localization extends the actual projective push along Q[t] to Q[t,t^-1]. -/
def localizedPush (h : PolynomialCompatible D K Q R i hi M P CQ CR) :
    LocalizedChow Q D K CQ → LocalizedChow R D K CR :=
  letI := polynomialModule Q D K CQ
  letI := polynomialModule R D K CR
  TensorProduct.map (LinearMap.id : Coefficients →ₗ[Polynomial ℚ] Coefficients)
    (polynomialPush D K Q R i hi M P CQ CR h)

end MathlibExt.AlgebraicGeometry.EquivariantProjectivePushModels
