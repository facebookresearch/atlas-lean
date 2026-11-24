/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CompactificationMetricExtensions
public import MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights

/-!
# Actual metrized line, rational model and point-height construction requests

All fibre maps retain actual local sections, native completed residue
fields and the same literal algebraic tensor, dual or pullback sheaf.
Rational models retain positive denominators, full compactification
metrics and the exact boundary Cauchy image.

Height admissibility remains a condition on actual fibre integrals;
it is not asserted for an arbitrary family of place metrics.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 2.1--2.2, 4.1--4.3 and A.5.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MetrizedLineOperations

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.ValuedLineFibres
open MathlibExt.AlgebraicGeometry.MetrizedLineOperationModels

/-- The actual algebraic dual is fixed by full module-sheaf evaluation. It needs no norm on `K`. -/
public def_wanted lineDual (K : Type) [Field K] (X : Over (Spec (.of K))) (L : X.left.Modules)
    (hL : IsLineBundle L) : DualLine K X L

variable (K : Type) [NormedField K] (X : Over (Spec (.of K)))
  (L M : X.left.Modules)

/-- The actual algebraic line isomorphism has its unique native completed-fibre map. -/
public def_wanted lineFibreIso (e : L ≅ M) : FibreIso K X L M e

/-- Construct the actual tensor fibre isomorphism from its native local-section tensor map. -/
public def_wanted lineTensorFibre (hL : IsLineBundle L) (hM : IsLineBundle M) :
    TensorFibre K X L M

/-- Construct tensor norms on the literal tensor line, normalized on every pure tensor. -/
public def_wanted lineTensorMetric (F : TensorFibre K X L M)
    (N : MetrizedLine K X L) (P : MetrizedLine K X M) : TensorMetric K X L M F N P

/-- Native dual fibre functionals of an invertible sheaf agree with actual
section-pair evaluation. -/
public def_wanted lineDualFibre (hL : IsLineBundle L) (D : DualLine K X L) : DualFibre K X L D

/-- Native operator norms give the metric on the same actual dual line. -/
public def_wanted lineDualMetric (D : DualLine K X L) (F : DualFibre K X L D)
    (N : MetrizedLine K X L) : DualMetric K X L D F N

/-- Scalar-extended native fibres retain every original residue-field unit. -/
public def_wanted linePullbackFibre {Y : Over (Spec (.of K))} (f : Y ⟶ X) :
    PullbackFibre K X L f

/-- Construct the metric on the actual algebraic pullback, with its full pure-tensor rule. -/
public def_wanted linePullbackMetric {Y : Over (Spec (.of K))} (f : Y ⟶ X)
    (F : PullbackFibre K X L f) (N : MetrizedLine K X L) : PullbackMetric K X L f F N

/-- Every line power retains actual local sections and completed-field scalar powers. -/
public def_wanted linePowerFibre (hL : IsLineBundle L) (n : ℕ) :
    MathlibExt.AlgebraicGeometry.MetrizedFibrePowerModels.PowerFibre K X L n

end WantedExt.AlgebraicGeometry.MetrizedLineOperations

namespace WantedExt.AlgebraicGeometry.MeasuredLinePointHeights

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

/-- The scheme-point pullback fibre has its actual basis and source-normalized place vectors. -/
public def_wanted rationalPointFrame {K : Type} [Field K] (A : AdelicField K)
    (X : Over (Spec (.of K))) (L : X.left.Modules) (hL : IsLineBundle L)
    (x : BasePoint (K := K) ⟶ X) : PointFrame A X L x

end WantedExt.AlgebraicGeometry.MeasuredLinePointHeights

namespace WantedExt.AlgebraicGeometry.RationalAdelicModelOperations

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.AdelicArithmeticModelFrames
open MathlibExt.AlgebraicGeometry.CompactificationMetricExtensions

/-- All original line powers retain their actual local section and completed scalar maps. -/
public def_wanted allPlacePower {K : Type} [Field K] (A : AdelicField K)
    (X : Over (Spec (.of K))) (L : X.left.Modules) (hL : IsLineBundle L) (n : ℕ) :
    MathlibExt.AlgebraicGeometry.RationalAdelicModelMetrics.AllPlacePower
      (A := A) (X := X) (L := L) n

/-- A supplied full compactification metric restricts by the actual native open and fibre maps. -/
public def_wanted compactificationRestriction {K : Type} [Field K] (A : AdelicField K)
    (X : Over (Spec (.of K))) (L : X.left.Modules) (M : ArithmeticModel A X L)
    (P : MetrizedLine A M.compactification (compactLine M)) :
    Σ N : MetrizedLine A X L,
      {E : Extension M N // E.metric = P}

end WantedExt.AlgebraicGeometry.RationalAdelicModelOperations
