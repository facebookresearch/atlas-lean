/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual LF distributions, support quotients and Wirtinger operators

Complex distributions are continuous complex-linear forms on the native
LF space of compactly supported smooth complex test functions. The
tempered section model is the quotient of global distributions by the
kernel of restriction to the specified open. Its subanalytic realization
uses finite subanalytic covers and retains these quotient maps.

The real directional derivative is minus the native test-function
transpose. Partial-z and partial-zbar are the original one-half
Wirtinger combinations. Local coefficient/operator actions require a
relatively compact subanalytic V inside the coefficient open U.

Source: DK arXiv:1311.2374v2, Definition 5.1.1(iii), Proposition 5.1.3,
Definition 5.2.1. Native LF test functions: Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 (Luigi Massacci, Anatole Dedecker),
Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TemperedDistributionSectionModels

open TopologicalSpace

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev ComplexTest (U : Opens E) := TestFunction U ℂ (⊤ : ℕ∞)

/-- The actual continuous LF test dual. -/
abbrev ComplexDistribution (U : Opens E) := ComplexTest E U →L[ℂ] ℂ

/-- The native inclusion of supported test functions, on their original values. -/
def testInclusion (U V : Opens E) (_h : V ≤ U) : ComplexTest E V →L[ℂ] ComplexTest E U :=
  TestFunction.monoCLM ℂ

/-- Restriction is precomposition with that exact test inclusion. -/
def restrictDistribution (U V : Opens E) (h : V ≤ U) :
    ComplexDistribution E U →ₗ[ℂ] ComplexDistribution E V where
  toFun T := T.comp (testInclusion E U V h)
  map_add' T S := by ext φ; rfl
  map_smul' a T := by ext φ; rfl

abbrev GlobalDistribution := ComplexDistribution E ⊤

/-- The original distributions supported outside the selected open. -/
def supportedOutside (U : Opens E) : Submodule ℂ (GlobalDistribution E) :=
  LinearMap.ker (restrictDistribution E ⊤ U le_top)

/-- Db^t(U) is the actual source quotient of global distribution sections. -/
abbrev TemperedSections (U : Opens E) := GlobalDistribution E ⧸ supportedOutside E U

def quotientProjection (U : Opens E) : GlobalDistribution E →ₗ[ℂ] TemperedSections E U :=
  (supportedOutside E U).mkQ

/-- The true negative test transpose, keeping the original LF topology. -/
def distributionDerivative (U : Opens E) (v : E) :
    ComplexDistribution E U →ₗ[ℂ] ComplexDistribution E U where
  toFun T := -T.comp (TestFunction.lineDerivCLM ℂ v)
  map_add' T S := by ext φ; simp [add_comm]
  map_smul' a T := by ext φ; simp

/-- Structural commutation for the already prescribed restriction/derivative. -/
structure DerivativeRestrictionSource : Prop where
  commute : ∀ (U V : Opens E) (h : V ≤ U) (v : E),
    (restrictDistribution E U V h).comp (distributionDerivative E U v) =
      (distributionDerivative E V v).comp (restrictDistribution E U V h)

/-- Descend an actual global operator through its original support kernel. -/
def descendOperator (U : Opens E) (L : GlobalDistribution E →ₗ[ℂ] GlobalDistribution E)
    (hL : supportedOutside E U ≤ (supportedOutside E U).comap L) :
    TemperedSections E U →ₗ[ℂ] TemperedSections E U :=
  Submodule.mapQ (supportedOutside E U) (supportedOutside E U) L hL

def temperedDerivative (S : DerivativeRestrictionSource E) (U : Opens E) (v : E) :
    TemperedSections E U →ₗ[ℂ] TemperedSections E U :=
  descendOperator E U (distributionDerivative E ⊤ v) (by
    intro T hT
    change restrictDistribution E ⊤ U le_top (distributionDerivative E ⊤ v T) = 0
    have h := LinearMap.congr_fun (S.commute ⊤ U le_top v) T
    change restrictDistribution E ⊤ U le_top T = 0 at hT
    simpa [hT] using h)

abbrev ComplexCoordinates (n : ℕ) := EuclideanSpace ℂ (Fin n)

def realCoordinate (n : ℕ) (j : Fin n) : ComplexCoordinates n := EuclideanSpace.single j 1

def imaginaryCoordinate (n : ℕ) (j : Fin n) : ComplexCoordinates n :=
  Complex.I • realCoordinate n j

/-- The actual complex Wirtinger derivative on the source support quotient. -/
def partialZ (n : ℕ) (S : DerivativeRestrictionSource (ComplexCoordinates n))
    (U : Opens (ComplexCoordinates n)) (j : Fin n) :
    TemperedSections (ComplexCoordinates n) U →ₗ[ℂ]
      TemperedSections (ComplexCoordinates n) U :=
  (1 / 2 : ℂ) • (temperedDerivative (ComplexCoordinates n) S U (realCoordinate n j) -
    Complex.I • temperedDerivative (ComplexCoordinates n) S U (imaginaryCoordinate n j))

/-- The conjugate derivative used by the actual tempered Dolbeault complex. -/
def partialZBar (n : ℕ) (S : DerivativeRestrictionSource (ComplexCoordinates n))
    (U : Opens (ComplexCoordinates n)) (j : Fin n) :
    TemperedSections (ComplexCoordinates n) U →ₗ[ℂ]
      TemperedSections (ComplexCoordinates n) U :=
  (1 / 2 : ℂ) • (temperedDerivative (ComplexCoordinates n) S U (realCoordinate n j) +
    Complex.I • temperedDerivative (ComplexCoordinates n) S U (imaginaryCoordinate n j))

end MathlibExt.AlgebraicGeometry.TemperedDistributionSectionModels
