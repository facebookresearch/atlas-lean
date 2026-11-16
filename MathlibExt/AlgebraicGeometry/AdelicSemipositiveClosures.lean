/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ArithmeticModelCurveDegrees
public import MathlibExt.AlgebraicGeometry.AdelicCompletionOperations
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Source-normalized strongly nef, nef and integrable adelic lines

Models are projective over the fixed integer or field ground base.
Arithmetic nefness uses the full model hermitian metric, its actual
standard archimedean places and point extensions, positive local frame
weights and arithmetic degrees of all closed integral curves. The
geometric field ground requires nonarchimedean places trivial on that
field and uses the literal coherent Euler degrees.

Strongly nef means the actual limit of nef rational models. Nef has
one strongly nef auxiliary line with aL+M strongly nef for every
positive integer a. Integrable is an actual completed-fibre isometry
to the difference of two strongly nef lines, using native tensor and
dual evaluation. These three source definitions remain distinct.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 1.1.4, 2.5 and A.4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdelicSemipositiveClosures

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open CoherentCurveLinearSeries PlacewiseMetrizedLineModels BoundaryMetricCompletionModels
open RationalAdelicModelMetrics AdelicCompletionOperations ArithmeticModelHermitianMetrics
open HermitianModelRestrictions

def gradedProjToSpec {R T : Type} [CommRing R] [CommRing T] [Algebra R T]
    (grading : ℕ → Submodule R T) [GradedAlgebra grading] : Proj grading ⟶ Spec (.of R) :=
  Proj.toSpecZero grading ≫ Spec.map (CommRingCat.ofHom (algebraMap ..))

/-- Projectivity is an actual closed embedding into the native homogeneous Proj. -/
def IsProjectiveOver {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of R)) : Prop :=
  letI := @MvPolynomial.gradedAlgebra
  ∃ (n : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)),
    IsClosedImmersion i ∧ i ≫ gradedProjToSpec _ = f

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules}

structure ArithmeticNefModel (m : ModelMetric (A := A) (X := X) (L := L)) where
  projective : IsProjectiveOver (integerMap m.integral.model.scheme)
  flat : Flat (integerMap m.integral.model.scheme)
  archimedean : ArchimedeanPoints (A := A) (X := X)
  hermitian : HermitianLine m.integral.model.line
  normalized : IsModelMetric m.integral.model hermitian m.integral.metric
  nef : ArithmeticModelCurveDegrees.IsNef m.integral.model.line hermitian

variable (k : Type) [Field k] (embedding : k →+* K)

/-- A geometric closed integral model curve and its actual coherent cohomology. -/
structure GeometricCurve (Y : Scheme.{0}) (f : Y ⟶ Spec (.of k)) (N : Y.Modules) where
  scheme : Scheme.{0}
  inclusion : scheme ⟶ Y
  [closed : IsClosedImmersion inclusion]
  [integral : IsIntegral scheme]
  [noetherian : IsNoetherian scheme]
  [proper : IsProper (inclusion ≫ f)]
  [finite_type : LocallyOfFiniteType (inclusion ≫ f)]
  dimension : Order.krullDim scheme = 1
  finiteH0 : FiniteDimensional k
    (cohomology (inclusion ≫ f) ((Scheme.Modules.pullback inclusion).obj N) 0)
  finiteH1 : FiniteDimensional k
    (cohomology (inclusion ≫ f) ((Scheme.Modules.pullback inclusion).obj N) 1)
  finiteO0 : FiniteDimensional k (cohomology (inclusion ≫ f) (structureModule scheme) 0)
  finiteO1 : FiniteDimensional k (cohomology (inclusion ≫ f) (structureModule scheme) 1)

structure GeometricNefModel (m : ModelMetric (A := A) (X := X) (L := L)) where
  nonarchimedean : ∀ (v : A.places) (a b : A.completion v), ‖a + b‖ ≤ max ‖a‖ ‖b‖
  trivial_on_ground : ∀ (v : A.places) (a : k), a ≠ 0 → ‖A.embedding v (embedding a)‖ = 1
  baseMap : m.integral.model.base.scheme ⟶ Spec (.of k)
  generic_normalized : m.integral.model.base.generic ≫ baseMap =
    Spec.map (CommRingCat.ofHom embedding)
  projective : IsProjectiveOver (m.integral.model.structureMap ≫ baseMap)
  nef : ∀ C : GeometricCurve k m.integral.model.scheme
    (m.integral.model.structureMap ≫ baseMap) m.integral.model.line,
    0 ≤ CoherentCurveLinearSeries.degree (C.inclusion ≫ m.integral.model.structureMap ≫ baseMap)
      ((Scheme.Modules.pullback C.inclusion).obj m.integral.model.line)

/-- The ground field and its actual scalar embedding are fixed for the entire approximation. -/
inductive GroundBase where
  | integers
  | geometric (k : Type) [Field k] (embedding : k →+* K)

def NefModel (G : GroundBase (K := K)) (m : ModelMetric (A := A) (X := X) (L := L)) : Type :=
  match G with
  | .integers => ArithmeticNefModel m
  | @GroundBase.geometric _ _ k inst embedding =>
    letI := inst
    GeometricNefModel k embedding m

variable (G : GroundBase (K := K)) (B : EffectiveBoundary A X)

def IsStronglyNef (m : AdelicMetric (L := L) B) : Prop :=
  ∃ S : ModelSequence (L := L) B, S.class = m.val ∧ ∀ n, Nonempty (NefModel G (S.model n))

def IsNef (m : AdelicMetric (L := L) B) : Prop :=
  ∃ (N : X.left.Modules) (n : AdelicMetric (L := N) B), IsStronglyNef G B n ∧
    ∀ (a : ℕ), 0 < a → ∃ (F : AllPlacePower (A := A) (X := X) (L := L) a)
      (P : PowerResult B m a F)
      (T : AllPlaceTensor (A := A) (X := X) (L := CurvePositivity.power L a) (M := N))
      (R : TensorResult B T P.metric n), IsStronglyNef G B R.metric

def IsIntegrable (m : AdelicMetric (L := L) B) : Prop :=
  ∃ (N P : X.left.Modules) (n : AdelicMetric (L := N) B) (p : AdelicMetric (L := P) B),
    IsStronglyNef G B n ∧ IsStronglyNef G B p ∧
      ∃ (D : AlgebraicDual (X := X) (L := P)) (F : AllPlaceDual (A := A) D)
        (d : DualResult B p D F)
        (T : AllPlaceTensor (A := A) (X := X) (L := N) (M := D.line))
        (r : TensorResult B T n d.metric), IsIsometric B m r.metric

end MathlibExt.AlgebraicGeometry.AdelicSemipositiveClosures
