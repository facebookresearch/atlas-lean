/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TorusBorelCoefficientModels

/-!
# Actual quotient-torus restriction and intrinsic partial degree

The quotient map is the actual T to T/A group-scheme projection.
Its continuous map is computed from its Laurent-coordinate matrix,
and the cohomology map is native Borel group-change pullback.
The degree filtration spans bounded character-polynomial multiples
of arbitrary quotient-torus classes. The quotient coefficients are
therefore absorbed before measuring A-degree, as in MO Section3.3.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.ResidualTorusDegreeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels TorusPolynomialDegreeModels
open IntegralChowChernModels ComplexAnalytification SymplecticTorusSourceModels
open CoefficientBettiModels TorusBorelCoefficientModels
open MathlibExt.Topology.ContinuousBorelGroupMaps
open scoped DirectSum

instance projectionGroupHom {A T : Over base} [GrpObj A] [GrpObj T]
    {S : Subtorus A T} (P : TorusSplitting S) : IsMonHom P.projection := by
  dsimp [TorusSplitting.projection]
  infer_instance

/-- The first projection belongs to the same actual group-scheme splitting. -/
def firstProjection {A T : Over base} [GrpObj A] [GrpObj T]
    {S : Subtorus A T} (P : TorusSplitting S) : T ⟶ A :=
  P.iso.hom ≫ fst A P.quotient

instance firstProjectionGroupHom {A T : Over base} [GrpObj A] [GrpObj T]
    {S : Subtorus A T} (P : TorusSplitting S) : IsMonHom (firstProjection P) := by
  dsimp [firstProjection]
  infer_instance

variable {A T : Over base} [GrpObj A] [GrpObj T]
  (MA : TorusModel A) (MT : TorusModel T) (S : Subtorus A T)
  (P : TorusSplitting S) (F : SchemeData) [ModObj T F.scheme]
  (AF : AnalyticTorusAction MT F.scheme)

/-- The residual action and its topology retain the original quotient group map. -/
structure ResidualGeometry where
  [action : ModObj P.quotient F.scheme]
  analytic : AnalyticTorusAction P.model F.scheme
  scheme : γ[T,F.scheme] = (P.projection ▷ F.scheme) ≫ γ[P.quotient,F.scheme]
  inclusion : TorusMorphismCoordinates MA MT S.inclusion
  coordinates : TorusMorphismCoordinates MT P.model P.projection
  topology : letI := AF.action
    letI := analytic.action
    ∀ (g : Fin MT.rank → ℂˣ) (z : space F.scheme),
      g • z = coordinates.groupMap g • z

variable (R : ResidualGeometry MA MT S P F AF)
variable {MA MT S P F AF}

abbrev QuotientH :=
  letI := R.action
  H P.model F.scheme R.analytic

/-- Pullback along the original quotient homomorphism acts on every actual Borel class. -/
def quotientClasses : QuotientH R →ₗ[ℂ] H MT F.scheme AF := by
  letI := AF.action
  letI := AF.continuous
  letI := R.action
  letI := R.analytic.action
  letI := R.analytic.continuous
  exact DirectSum.toModule ℂ ℤ (BorelCohomologyModels.GradedH
    (Fin MT.rank → ℂˣ) (space F.scheme)) (fun n =>
      (DirectSum.lof ℂ ℤ (BorelCohomologyModels.H (Fin MT.rank → ℂˣ) (space F.scheme)) n).comp
        (cohomologyPullback ℂ
          (borelHom R.coordinates.groupMap R.coordinates.groupMap_continuous
            (𝟙 (space F.scheme)) R.topology) n))

variable (C : CoefficientCoordinates MT) (ρ : PolynomialAction MT C F.scheme AF)

/-- This is the quotient-coefficient span of character polynomials of bounded total degree. -/
def degreeFiltration (d : ℕ) : Submodule ℂ (H MT F.scheme AF) :=
  Submodule.span ℂ {a | ∃ (p : CharacterPolynomials MT.rank)
    (gamma : QuotientH R),
    p.totalDegree ≤ d ∧ a = ρ.action p (quotientClasses R gamma)}

/-- Zero has degree minus infinity, including components of codimension zero. -/
def strictHalfDegree (codimension : ℕ) (a : H MT F.scheme AF) : Prop :=
  a=0 ∨ ∃ d : ℕ, 2*d<codimension ∧
    a ∈ degreeFiltration R C ρ d

end MathlibExt.AlgebraicGeometry.ResidualTorusDegreeModels
