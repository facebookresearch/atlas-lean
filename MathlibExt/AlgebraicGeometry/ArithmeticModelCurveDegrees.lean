/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HermitianModelRestrictions
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Field.ZMod

/-!
# Literal degrees of arithmetic model curves

A vertical degree is the actual coherent Euler degree over F_p times
log p. A horizontal degree uses an actual nonzero integral section:
logarithm of the cardinality of its native global-section cokernel,
minus the logarithmic norm summed over every scheme-valued complex
embedding. Conjugate embeddings are both present; no extra factor two
is inserted.

The independence of this integral section, pullback of hermitian norms,
and geometric existence/classification data are separate requests.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections A.2 and A.4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ArithmeticModelCurveDegrees

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open CoherentCurveLinearSeries ArithmeticModelHermitianMetrics
open HermitianModelRestrictions ComplexAnalytification GenericSectionMaps

/-- An actual closed integral curve of the full arithmetic model. -/
structure ModelCurve (Y : Scheme.{0}) where
  scheme : Scheme.{0}
  inclusion : scheme ⟶ Y
  [closed : IsClosedImmersion inclusion]
  [integral : IsIntegral scheme]
  [noetherian : IsNoetherian scheme]
  [proper : IsProper (integerMap scheme)]
  dimension : Order.krullDim scheme = 1

attribute [instance] ModelCurve.closed ModelCurve.integral ModelCurve.noetherian ModelCurve.proper

variable {Y : Scheme.{0}} (C : ModelCurve Y) (L : Y.Modules)

def curveLine : C.scheme.Modules := (Scheme.Modules.pullback C.inclusion).obj L

/-- The vertical curve keeps its actual residue characteristic and finite coherent cohomology:
a proper curve over `𝔽_p` on which the restricted line is invertible. -/
structure Vertical (p : ℕ) [Fact p.Prime] where
  structureMap : C.scheme ⟶ Spec (.of (ZMod p))
  [curve : IsProperCurve structureMap]
  line : IsLineBundle (curveLine C L)
  finiteH0 : FiniteDimensional (ZMod p) (cohomology structureMap (curveLine C L) 0)
  finiteH1 : FiniteDimensional (ZMod p) (cohomology structureMap (curveLine C L) 1)
  finiteO0 : FiniteDimensional (ZMod p) (cohomology structureMap (structureModule C.scheme) 0)
  finiteO1 : FiniteDimensional (ZMod p) (cohomology structureMap (structureModule C.scheme) 1)

attribute [instance] Vertical.curve

/-- The vertical degree `deg_{𝔽_p}(L|_C) · log p`. -/
def verticalDegree {p : ℕ} [Fact p.Prime] (V : Vertical C L p) : ℝ :=
  (CoherentCurveLinearSeries.degree V.structureMap (curveLine C L) V.line : ℝ) * Real.log p

/-- Horizontal curves are finite flat over the actual integer base. -/
structure Horizontal : Prop where
  [finite : IsFinite (integerMap C.scheme)]
  [flat : Flat (integerMap C.scheme)]
  [characteristic : CharZero Γ(C.scheme,⊤)]
  [complex_finite : Finite (ComplexPoints (complexScheme C.scheme).hom)]

/-- The literal native quotient by the integral section, with no chosen divisor carrier. -/
def sectionCokernel (s : structureModule C.scheme ⟶ curveLine C L) : Type :=
  Γ(curveLine C L,⊤) ⧸ LinearMap.range ((s.val.app (op ⊤)).hom)

structure HorizontalSection where
  sectionMap : structureModule C.scheme ⟶ curveLine C L
  injective : Function.Injective ((sectionMap.val.app (op ⊤)).hom)
  [finite_cokernel : Finite (sectionCokernel C L sectionMap)]
  nonzero : ∀ p : ComplexPoints (complexScheme C.scheme).hom,
    ∀ D : PointDictionary (complexScheme C.scheme),
      ValuedLineFibres.evaluateSection _ _ _
        (complexSection ⊤ (homSection (Over.mk (integerMap C.scheme)) sectionMap))
        (D.point p) (by simp) ≠ 0

attribute [instance] HorizontalSection.finite_cokernel

def horizontalLogNorm (H : HermitianLine (curveLine C L)) (s : HorizontalSection C L)
    (p : ComplexPoints (complexScheme C.scheme).hom) : ℝ :=
  Real.log ((H.metric.fibreNorm (H.dictionary.point p)).norm
    (ValuedLineFibres.evaluateSection _ _ _
      (complexSection ⊤ (homSection (Over.mk (integerMap C.scheme)) s.sectionMap))
      (H.dictionary.point p) (by simp)))

def horizontalDegree (Q : Horizontal C) (H : HermitianLine (curveLine C L))
    (s : HorizontalSection C L) : ℝ := by
  letI := Q.complex_finite
  letI := Fintype.ofFinite (ComplexPoints (complexScheme C.scheme).hom)
  exact Real.log (Nat.card (sectionCokernel C L s.sectionMap)) -
    ∑ p : ComplexPoints (complexScheme C.scheme).hom, horizontalLogNorm C L H s p

/-- Arithmetic nefness tests every vertical and horizontal closed integral model curve. -/
def IsNef (H : HermitianLine L) : Prop :=
  IsSemipositive H ∧
    (∀ (C : ModelCurve Y) (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ V : Vertical C L p, 0 ≤ verticalDegree C L V) ∧
    (∀ (C : ModelCurve Y) (Q : Horizontal C) (P : HermitianPullback C.inclusion H)
      (s : HorizontalSection C L), 0 ≤ horizontalDegree C L Q P.hermitian s)

end MathlibExt.AlgebraicGeometry.ArithmeticModelCurveDegrees
