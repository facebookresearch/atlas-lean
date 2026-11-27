/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdelicModelMetricSequences
public import MathlibExt.AlgebraicGeometry.MetrizedFibrePowerModels
public import MathlibExt.AlgebraicGeometry.CompactificationMetricExtensions

/-!
# Actual rational model metrics and their boundary completion

A rational approximation uses one genuine arithmetic model of eL for a
positive integer e and the e-th-root metric on the original line L.
The power map is normalized on every actual pulled-back local section.
All approximation models retain one common arithmetic base.

The resulting adelic metrics are the literal image in the already
computed boundary Cauchy quotient. Integral model sequences are its
denominator-one subcase, rather than the definition of every rational
model approximation.

Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 1.1.3--1.1.4,
2.1--2.2; the positive integer e is retained explicitly.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RationalAdelicModelMetrics

open CategoryTheory Opposite _root_.AlgebraicGeometry
open PlacewiseMetrizedLineModels CoherentCurveLinearSeries
open BoundaryMetricCompletionModels AdelicArithmeticModelFrames
open GenericSectionMaps MetrizedFibrePowerModels

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules}

/-- Every original section pulls back by the actual module adjunction unit. -/
def placeSection (U : X.left.Opens) (s : Γ(L,U)) (v : A.places) :
    Γ(placeLine A X L v, placeProjection A X v ⁻¹ᵁ U) :=
  localPullbackSection (placeProjection A X v) L U (placeProjection A X v ⁻¹ᵁ U)
    (by rfl) s

/-- The actual global line-power map is fixed on every local section and completed scalar. -/
structure AllPlacePower (n : ℕ) where
  map : ∀ (v : A.places) (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)),
    ValuedLineFibres.Fibre (A.completion v) (placeScheme A X v) (placeLine A X L v) p →
      ValuedLineFibres.Fibre (A.completion v) (placeScheme A X v)
        (placeLine A X (CurvePositivity.power L n) v) p
  homogeneous : ∀ (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v))
    (a : ValuedLineFibres.CompletedResidue (A.completion v) (placeScheme A X v) p)
    (z : ValuedLineFibres.Fibre (A.completion v) (placeScheme A X v) (placeLine A X L v) p),
    map v p (a • z) = a ^ n • map v p z
  section_normalized : ∀ (U : X.left.Opens) (s : Γ(L,U)) (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v))
    (hp : placeProjection A X v p.schemePoint ∈ U),
    map v p (ValuedLineFibres.evaluateSection _ _ _ (placeSection U s v) p hp) =
      ValuedLineFibres.evaluateSection _ _ _
        (placeSection U (powerSectionAt L U s n) v) p hp
  nonzero : 0 < n → ∀ v p z, z ≠ 0 → map v p z ≠ 0

/-- A genuine positive-denominator model approximation of the original line. -/
structure ModelMetric where
  denominator : ℕ+
  integral : AdelicModelMetricSequences.ModelMetric
    (A := A) (X := X) (L := CurvePositivity.power L denominator)
  compactification : CompactificationMetricExtensions.Extension integral.model integral.metric
  metric : MetrizedLine A X L
  power : AllPlacePower (A := A) (X := X) (L := L) denominator
  root_normalized : ∀ (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)) (z : Fibre metric v p),
    norm integral.metric v p (power.map v p z) = norm metric v p z ^ (denominator : ℕ)

/-- Rational model sequences retain a common actual arithmetic base and the exact boundary gauge. -/
structure ModelSequence (B : EffectiveBoundary A X) where
  base : ArithmeticBase A
  model : ℕ → ModelMetric (A := A) (X := X) (L := L)
  common_base : ∀ n, (model n).integral.model.base = base
  cauchy : IsCauchy B (fun n ↦ (model n).metric)

/-- Its exact source sequence in the original native Cauchy type. -/
def ModelSequence.toCauchy {B : EffectiveBoundary A X} (S : ModelSequence (L := L) B) :
    CauchySequence (L := L) B := ⟨fun n ↦ (S.model n).metric, S.cauchy⟩

/-- The actual boundary completion class of the rational model sequence. -/
def ModelSequence.class {B : EffectiveBoundary A X} (S : ModelSequence (L := L) B) :
    BoundaryMetricCompletion (L := L) B := Quotient.mk _ S.toCauchy

/-- Rational-model metrics of the fixed-gauge completion: the literal image of the rational
model sequences in this same completion (not Yuan--Zhang's adelic metrics, whose boundary
topology is not used here). -/
def FixedGaugeAdelicMetric (B : EffectiveBoundary A X) :=
  {m : BoundaryMetricCompletion (L := L) B // ∃ S : ModelSequence (L := L) B, S.class = m}

end MathlibExt.AlgebraicGeometry.RationalAdelicModelMetrics
