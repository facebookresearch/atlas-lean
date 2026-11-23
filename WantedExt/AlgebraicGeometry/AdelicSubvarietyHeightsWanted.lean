/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AdelicSubvarietyHeights

/-!
# Actual closed-image and numerical height construction requests

Degrees are native coherent/generic-forgetful model limits, never assigned
open numbers. Vector numerators are actual metric Deligne classes on the
same closed image; numerical numerators are actual model intersections.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 5.3.1--5.3.3, pp152--154.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AdelicSubvarietyHeights

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AdelicSubvarietyHeights AdelicPicardVectors AdelicSemipositiveClosures PlacewiseMetrizedLineModels
open NumericalAdelicIntersections RelativeDeterminantPairings

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

variable {K : Type} [Field K] {A : AdelicField K} {X T : Over (Spec (.of K))}

/-- The image retains all actual regular-function kernels, rather than a selected closed subset. -/
public def_wanted closedImage (u : T ⟶ X) [IsIntegral T.left] [IsProper T.hom]
    (scope : QuasiProjectiveScope X) :
    Σ n : ℕ, ClosedImage u n

public def_wanted vectorSources (G : GroundBase (K := K)) (u : T ⟶ X) (n : ℕ)
    (C : ClosedImage u n) (M : LineObject (A := A) (X := X) G)
    (B : AdelicArithmeticModelFrames.ArithmeticBase A) (b : ℕ+) (ground : GroundModel G B b) :
    VectorSources G C M

/-- Actual global arithmetic/geometric model intersection construction. -/
public def_wanted numericalIntersections (G : GroundBase (K := K)) (t : ℕ)
    (M : Fin t → LineObject (A := A) (X := X) G)
    [IsIntegral X.left] [LocallyOfFiniteType X.hom] (scope : QuasiProjectiveScope X)
    (n : ℕ) (dimension : IsPureRelativeDimension X.hom n)
    (B : AdelicArithmeticModelFrames.ArithmeticBase A) (b : ℕ+) (ground : GroundModel G B b)
    (arity : t = n+b) : NumericalAdelicIntersections.Sources G M

public theorem_wanted numericalConvergence (G : GroundBase (K := K)) (t : ℕ)
    (M : Fin t → LineObject (A := A) (X := X) G) (S : NumericalAdelicIntersections.Sources G M) :
    NumericalAdelicIntersections.Convergence S

/-- Nonproper Moriwaki height retains actual source base polarizations and SAME generic degree. -/
public def_wanted numericalSources (G : GroundBase (K := K)) (n : ℕ) (Z : ClosedSubvariety X n)
    (M : LineObject (A := A) (X := X) G)
    (B : AdelicArithmeticModelFrames.ArithmeticBase A) (b : ℕ+) (ground : GroundModel G B b)
    (H : Fin (b-1) → LineObject (A := A) (X := MeasuredLinePointHeights.BasePoint (K := K)) G)
    (scope : QuasiProjectiveScope Z.scheme) : NumericalSources G Z M b H

end WantedExt.AlgebraicGeometry.AdelicSubvarietyHeights
