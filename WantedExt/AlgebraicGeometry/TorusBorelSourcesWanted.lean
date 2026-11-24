/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.TorusSupportedCorrespondenceModels
public import MathlibExt.AlgebraicGeometry.ResidualTorusDegreeModels

/-!
# Native Borel, character, Euler and supported-trace construction requests

Each output preserves the actual scheme action, coordinate characters,
module descent and native cohomology maps. Quotient stages choose their
compatible diagonal action. Bundle and proper-map hypotheses retain
the source finite-dimensional complex geometry. These are shared
construction and coherence requests, independent of the Stab theorem.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.TorusBorelSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels IntegralChowChernModels
open SymplecticTorusSourceModels FiniteTorusBorelApproximationModels ComplexAnalytification
open CoefficientProperDualityModels TorusBorelEulerModels TorusBorelCoefficientModels
open ResidualTorusDegreeModels TorusSupportedCorrespondenceModels

def_wanted actual_analytic_torus_action (T : Over base) [GrpObj T] (M : TorusModel T)
    (X : SchemeData) [ModObj T X.scheme] : AnalyticTorusAction M X.scheme

def_wanted actual_mixed_approximation (T : Over base) [GrpObj T] (M : TorusModel T)
    (X : SchemeData) [ModObj T X.scheme] [IsSeparated X.scheme.hom]
    (AX : AnalyticTorusAction M X.scheme) (m : ℕ) : MixedApproximationSource M X AX m

def_wanted actual_coordinate_cohomology (T : Over base) [GrpObj T] (M : TorusModel T) :
    CoefficientCoordinates M

def_wanted actual_polynomial_coefficient_action (T : Over base) [GrpObj T] (M : TorusModel T)
    (P : CoefficientCoordinates M) (X : SchemeData) [ModObj T X.scheme]
    (AX : AnalyticTorusAction M X.scheme) : PolynomialAction M P X.scheme AX

def_wanted actual_zero_section_euler_geometry (O : OrientationData) (X : SchemeData)
    [IsSeparated X.scheme.hom] [QuasiCompact X.scheme.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.scheme.hom]
    (E : X.scheme.left.Modules) (r : ℕ) (_bundle : AlgebraicBundleGeometry.IsBundle E r) :
    {G : ZeroEulerGeometry O X E r // G.dimension = d}

def_wanted actual_proper_coefficient_pullback (X Y : SchemeData)
    [IsSeparated X.scheme.hom] [IsSeparated Y.scheme.hom]
    (f : Y.scheme ⟶ X.scheme) [IsProper f.left] : ProperPullback ℂ (spaceMap f)

def_wanted actual_associated_bundle_module (T : Over base) [GrpObj T] (M : TorusModel T)
    (X : SchemeData) [ModObj T X.scheme] (AX : AnalyticTorusAction M X.scheme) (m : ℕ)
    [ModObj T (MixedTotal M X m)] (A : AnalyticTorusAction M (MixedTotal M X m))
    (P : MixedStage M X AX m A) (E : X.scheme.left.Modules) (r : ℕ)
    (_bundle : AlgebraicBundleGeometry.IsBundle E r) (L : LinearizedLineBundles.Linearization T
      X.scheme E) :
    AssociatedModule M X AX m A P L

def_wanted actual_residual_torus_geometry (A T : Over base) [GrpObj A] [GrpObj T]
    (MA : TorusModel A) (MT : TorusModel T) (S : Subtorus A T) (P : TorusSplitting S)
    (F : SchemeData) [ModObj T F.scheme] (AF : AnalyticTorusAction MT F.scheme)
    (_fixed : (S.inclusion ▷ F.scheme) ≫ γ[T,F.scheme] = snd A F.scheme) :
    ResidualGeometry MA MT S P F AF

theorem_wanted actual_degree_splitting_independence (A T : Over base) [GrpObj A] [GrpObj T]
    (MA : TorusModel A) (MT : TorusModel T) (S : Subtorus A T)
    (F : SchemeData) [ModObj T F.scheme] (AF : AnalyticTorusAction MT F.scheme)
    (P Q : TorusSplitting S) (RP : ResidualGeometry MA MT S P F AF)
    (RQ : ResidualGeometry MA MT S Q F AF) (C : CoefficientCoordinates MT)
    (rho : PolynomialAction MT C F.scheme AF) (d : ℕ) :
    degreeFiltration RP C rho d = degreeFiltration RQ C rho d

def_wanted actual_supported_finite_maps (T : Over base) [GrpObj T] (M : TorusModel T)
    (X Z C : SchemeData) [ModObj T X.scheme] [ModObj T Z.scheme] [ModObj T C.scheme]
    (AX : AnalyticTorusAction M X.scheme) (AZ : AnalyticTorusAction M Z.scheme)
    (AC : AnalyticTorusAction M C.scheme)
    (i : C.scheme ⟶ X.scheme ⊗ Z.scheme) [IsClosedImmersion i.left]
    [IsProper (i ≫ fst X.scheme Z.scheme).left]
    (_first : γ[T,C.scheme] ≫ (i ≫ fst X.scheme Z.scheme) =
      (T ◁ (i ≫ fst X.scheme Z.scheme)) ≫ γ[T,X.scheme])
    (_second : γ[T,C.scheme] ≫ (i ≫ snd X.scheme Z.scheme) =
      (T ◁ (i ≫ snd X.scheme Z.scheme)) ≫ γ[T,Z.scheme])
    (m : ℕ) [ModObj T (MixedTotal M X m)] [ModObj T (MixedTotal M Z m)]
    [ModObj T (MixedTotal M C m)]
    (MX : AnalyticTorusAction M (MixedTotal M X m))
    (MZ : AnalyticTorusAction M (MixedTotal M Z m))
    (MC : AnalyticTorusAction M (MixedTotal M C m))
    (PX : MixedStage M X AX m MX) (PZ : MixedStage M Z AZ m MZ)
    (PC : MixedStage M C AC m MC) : FiniteSupportedMaps M X Z C AX AZ AC i m MX MZ MC PX PZ PC

end WantedExt.AlgebraicGeometry.TorusBorelSources
