/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HallLaurentCompletion
public import MathlibExt.AlgebraicGeometry.StackBehrendModels

/-!
# Generator-normalized canonical Behrend integration and its completion

The integration output is fixed on EVERY actual homogeneous regular
scheme generator by its native constructible compact-support Betti
Euler sum and the actual numerical monomial. Lefschetz denominator
stages specialize to one. The projective-space inverse scalar action
specializes to the literal inverse of χ(P^k)=k+1, retaining the v3
coefficient correction.

The map's construction and Poisson laws are separate requests.
The completed map is computed coefficient by coefficient on the
actual numerically homogeneous regular Laurent functions. Its
support bound follows from linearity and the original support.

Reference: Bridgeland, arXiv:1002.4374v3, Theorem 5.1,
equation (25), §5.2 and corrected coefficient ring (50).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HallBehrendIntegrationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open GeometricHallStackFunctions HallFamilyStackModels HallConvolutionOperations
open HallSemiclassicalOperations HallProjectiveInverseModels
open HallNumericalGradingModels HallLaurentCompletion StackBehrendModels
open ConstructibleEulerCharacteristics StablePairFamilies

variable {X : Over (Spec (.of ℂ))} {HX : Threefold X} {N : NumericalData X HX}
  {H : HallStacks X} {D : ConvolutionModels H} {h : ConvolutionDescent D}
  {L : ∀ g : Generator H.moduli, LefschetzProduct g} {hL : LefschetzDescent L}

/-- A construction output fixed on actual generators and actual corrected coefficient actions. -/
structure NormalizedIntegration (C : RegularClosure h hL) (P : NumericalProjectionData N H)
    (W : StackBehrendModel H.families.carrier) where
  map : Semiclassical C →ₗ[ℂ] NumericalAlgebra N
  generator : ∀ (α : Delta N) (g : Generator H.moduli) (S : SchemeSource g.source)
    (_homogeneous : HomogeneousGenerator (P.component α) g) (n : ℕ)
    (E : EulerPresentation S.scheme (pulledStackWeight W g S)),
    map ((semiclassicalRelations C).mkQ (regularSymbol g S n)) =
      (weightedGenerator W g S E : ℂ) • (AddMonoidAlgebra.single α (1 : ℂ) : NumericalAlgebra N)
  projectiveInverse : ∀ (k : ℕ) (J : ProjectiveInverseModel k)
    (Q : ScalarProductModels H.moduli J.inverseStack) (hQ : ScalarDescent Q)
    (a : Regular H.moduli),
    map ((semiclassicalRelations C).mkQ
      ⟨scalarAction hQ a.val,projectiveInverse_regular k J Q hQ a⟩) =
    (((k+1 : ℕ) : ℂ)⁻¹) • map ((semiclassicalRelations C).mkQ a)

/-- The literal completed integration coefficient in its actual numerical monomial. -/
def completedIntegrationValue {C : RegularClosure h hL} {P : NumericalProjectionData N H}
    {W : StackBehrendModel H.families.carrier} (I : NormalizedIntegration C P W)
    (a : RegularHallSeries H P) (α : Delta N) : ℂ :=
  (I.map ((semiclassicalRelations C).mkQ (regularCoefficient a α))).coeff α

/-- Linearity cannot enlarge the bounded-below χ support. -/
theorem completedIntegration_support {C : RegularClosure h hL} {P : NumericalProjectionData N H}
    {W : StackBehrendModel H.families.carrier} (I : NormalizedIntegration C P W)
    (a : RegularHallSeries H P) : LaurentSet N {α | completedIntegrationValue I a α≠0} := by
  intro β
  apply (a.support β).mono
  rintro n ⟨α,hα,hn⟩
  refine ⟨α,?_,hn⟩
  intro hz
  have he : regularCoefficient a α=0 := Subtype.ext hz
  apply hα
  simp [completedIntegrationValue,he]

/-- The completed target is the actual complex Laurent coefficient function. -/
def completedIntegration {C : RegularClosure h hL} {P : NumericalProjectionData N H}
    {W : StackBehrendModel H.families.carrier} (I : NormalizedIntegration C P W)
    (a : RegularHallSeries H P) : LaurentFunction N ℂ :=
  ⟨completedIntegrationValue I a,completedIntegration_support I a⟩

end MathlibExt.AlgebraicGeometry.HallBehrendIntegrationModels
