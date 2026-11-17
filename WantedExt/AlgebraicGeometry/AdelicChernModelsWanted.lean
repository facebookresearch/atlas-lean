/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NumericalAdelicIntersections

/-!
# Actual local/global Chern construction and mass requests

All requests retain the native models, original scalars, genuine atlases,
compact-test convergence and normalization. Atomic points have a discrete
valuation guard. Nonproper mass has the precise Lemma 5.4.4 global-field
guard. These are direct unfinished construction/proof requests, not
completed providers and not interface completion gates.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 3.6 and 4.1,
Appendix A.6.2 and Lemma 5.4.4, pp170--171.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AdelicChernModels

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PlacewiseMetrizedLineModels AdelicSemipositiveClosures AdelicPicardVectors
open AdelicChernLimits NumericalAdelicIntersections ModelIntersectionDegrees
open RelativeDeterminantPairings

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

public def_wanted valuationResidue (K : Type) [NormedField K]
    (h : ∀ a b : K, ‖a+b‖ ≤ max ‖a‖ ‖b‖) :
    NonarchimedeanChernModels.ValuationResidue K h

/-- Actual model component DVRs, only in the discrete valuation illustration. -/
public def_wanted divisorialPoints (K : Type) [NormedField K] [CompleteSpace K]
    (X : Over (Spec (.of K))) [IsIntegral X.left]
    (h : ∀ a b : K, ‖a+b‖ ≤ max ‖a‖ ‖b‖) (d : ℕ) (L : Fin d → X.left.Modules)
    (M : NonarchimedeanChernModels.ModelTuple K X h d L)
    (normal : ∀ y : M.scheme, IsDomain (M.scheme.presheaf.stalk y) ∧
      IsIntegrallyClosed (M.scheme.presheaf.stalk y))
    (V : NonarchimedeanChernModels.ValuationResidue K h)
    (S : NonarchimedeanChernModels.SpecialComponents M V)
    (v : NonarchimedeanChernModels.DiscreteValuation K) :
    ∀ C, NonarchimedeanChernModels.DivisorialPoint M V S v C

public def_wanted modelIntersection (K : Type) [NormedField K] [CompleteSpace K]
    (X : Over (Spec (.of K))) (h : ∀ a b : K, ‖a+b‖ ≤ max ‖a‖ ‖b‖)
    (d : ℕ) (L : Fin d → X.left.Modules)
    (M : NonarchimedeanChernModels.ModelTuple K X h (d+1)
      (Fin.cons (CoherentCurveLinearSeries.structureModule X.left) L)) :
    NonarchimedeanChernModels.ModelIntersectionSource M

public def_wanted nonarchMeasure (K : Type) [NormedField K]
    (X : Over (Spec (.of K))) (h : ∀ a b : K, ‖a+b‖ ≤ max ‖a‖ ‖b‖)
    (d : ℕ) (L : Fin d → X.left.Modules)
    (H : ∀ i, ValuedLineFibres.MetrizedLine K X (L i))
    (S : NonarchimedeanChernModels.CompactTestSources (K := K) (X := X) (hK := h) H) :
    NonarchimedeanChernModels.ChernMeasureParts S

public def_wanted archMeasure (Y : Over (Spec (.of ℂ))) (d : ℕ)
    (L : Fin d → Y.left.Modules) (H : ∀ i, ArchimedeanChernModels.ComplexMetric (L i))
    (S : ArchimedeanChernModels.GlobalSources Y d L H) :
    ArchimedeanChernModels.ChernMeasureParts S

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}

/-- Choose faithful model sources from actual integrable classes; arbitrary
model representatives need not themselves have integrable local metrics. -/
public def_wanted adelicSources (G : GroundBase (K := K)) (d : ℕ)
    (M : Fin d → LineObject (A := A) (X := X) G) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (quasiProjective : QuasiProjectiveScope X)
    (dimension : IsPureRelativeDimension X.hom d)
    (B : AdelicArithmeticModelFrames.ArithmeticBase A) (b : ℕ+) (ground : GroundModel G B b)
    (nontrivial : ∀ v : A.places, ∃ a : A.completion v, ‖a‖ ≠ 0 ∧ ‖a‖ ≠ 1) :
    Σ F : GenericModelSources G M, ChernSources M F

public proof_wanted genericDegreeConvergence (G : GroundBase (K := K)) (d : ℕ)
    (M : Fin d → LineObject (A := A) (X := X) G) (F : GenericModelSources G M) :
    GenericDegreeConvergence F

public def_wanted signedMeasure (G : GroundBase (K := K)) (d : ℕ)
    (M : Fin d → LineObject (A := A) (X := X) G) (F : GenericModelSources G M)
    (S : ChernSources M F) : SignedChernMeasure S

public def_wanted positiveMeasure (G : GroundBase (K := K)) (d : ℕ)
    (M : Fin d → LineObject (A := A) (X := X) G)
    (nef : ∀ i, IsNef G (M i).boundary (M i).metric)
    (F : GenericModelSources G M) (S : ChernSources M F) (v : A.places) :
    PositiveChernMeasure S v

/-- The SAME measure, the SAME degree, and the precise proper/global-field scope. -/
public proof_wanted mass (G : GroundBase (K := K)) (d : ℕ)
    (M : Fin d → LineObject (A := A) (X := X) G)
    (F : GenericModelSources G M) (S : ChernSources M F) (v : A.places)
    (P : PositiveChernMeasure S v) (guard : MassScope G X) : MassIdentity P guard

end WantedExt.AlgebraicGeometry.AdelicChernModels
