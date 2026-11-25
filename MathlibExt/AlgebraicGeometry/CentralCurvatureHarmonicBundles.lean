/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
public import MathlibExt.AlgebraicGeometry.CoordinateFormIntegrals
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Degree-normalized central curvature and twisted harmonic bundles

For the convention nabla=d+A and c1=(i/2pi)tr(F), the central curvature
of degree d and rank r is -2pi i(d/r)(omega/integral omega) times identity.
The area is the actual coordinate-partition integral of the positive
Kähler form. The normalized first-Chern form integrates to d.

The chosen puncture-loop convention gives exp(2pi i d/r) times identity;
rank two and degree one therefore give -I. The matrices are never used
as a replacement for the actual connection or its horizontal realization.

Source: de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2, Introduction,
printed page 3, fixes the rank-two degree-one monodromy -I and the loop
a1^-1 b1^-1 a1 b1 ... ag^-1 bg^-1 ag bg around the puncture. The curvature
sign is the explicit c1/connection convention here. Simpson,
alg-geom/9604005v1, section 2, supplies the harmonic decomposition.
The actual integration source credits remain in CoordinateFormIntegrals.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CentralCurvatureHarmonicBundles

open _root_.CategoryTheory KahlerClassGeometry ManifoldDifferentialForms CoordinateFormIntegrals
open SmoothHarmonicBundleGeometry
open scoped Manifold ContDiff Matrix Matrix.Norms.Elementwise

variable (M : Type) [TopologicalSpace M] [ChartedSpace (Coordinates 1) M]
  [IsManifold 𝓘(ℝ, Coordinates 1) ∞ M] [IsManifold 𝓘(ℂ, Coordinates 1) ∞ M]
  [ExteriorTheory ℝ (Coordinates 1) M]

structure CurveNormalization where
  coordinates : RealCoordinateMap 1
  atlas : IntegrationAtlas 1 M
  kahler : KahlerStructure 1 M
  area_positive : 0 < integral 1 M coordinates atlas kahler.form.val

variable {M} (P : CurveNormalization M)

def area : ℝ := integral 1 M P.coordinates P.atlas P.kahler.form.val

def centralScalar (d : ℤ) (r : ℕ) : ℂ :=
  -(2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((d : ℂ) / (r : ℂ)) / (area P : ℂ)

def centralCurvatureValue (d : ℤ) (r : ℕ) (x : M) (u v : Coordinates 1) : Matrices r :=
  (centralScalar P d r * (evaluateTwoForm 1 M P.kahler.form.val x u v : ℂ)) • (1 : Matrices r)

def degreeForm (d : ℤ) : GlobalForms ℝ (Coordinates 1) M 2 :=
  ((d : ℝ) / area P) • P.kahler.form.val

def closedDegreeForm (d : ℤ) : closedForms ℝ (Coordinates 1) M 2 :=
  ((d : ℝ) / area P) • P.kahler.form

def degreeChernClass (d : ℤ) : DeRhamH2 ℝ (Coordinates 1) M :=
  classOfClosedTwoForm ℝ (Coordinates 1) M (closedDegreeForm P d)

theorem central_trace_normalization (d : ℤ) (r : ℕ) (hr : 0 < r)
    (x : M) (u v : Coordinates 1) :
    (Complex.I / ((2 : ℂ) * (Real.pi : ℂ))) * Matrix.trace (centralCurvatureValue P d r x u v) =
      ((d : ℂ) / (area P : ℂ)) * (evaluateTwoForm 1 M P.kahler.form.val x u v : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have ha : (area P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt P.area_positive)
  simp only [centralCurvatureValue, centralScalar, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]
  field_simp
  simp [Complex.I_sq]

variable [IntegrationTheory 1 M P.coordinates P.atlas]

theorem integral_degreeForm (d : ℤ) : integral 1 M P.coordinates P.atlas (degreeForm P d) = d := by
  rw [degreeForm, IntegrationTheory.smul]
  change ((d : ℝ) / area P) * area P = d
  exact div_mul_cancel₀ _ (ne_of_gt P.area_positive)

variable {r : ℕ} (B : SmoothComplexBundle 1 M r)

/-- The connection has the degree-`d` normalized central curvature: the bundle has positive rank
`r` and on every trivializing chart the curvature is `-2πi (d/r) (ω / ∫ω)` times the identity. This
prescribed central curvature is stronger than projective flatness (scalar curvature), which every
rank-one connection has. -/
def HasNormalizedCentralCurvature (d : ℤ) (A : SmoothConnection B) : Prop :=
  0 < r ∧ ∀ i x, x ∈ B.core.baseSet i → ∀ u v,
    curvatureValue B A.value i x u v = centralCurvatureValue P d r x u v

/-- A metric whose reconstructed connection has the degree-`d` normalized central curvature, on a
bundle of positive rank. -/
def IsCentralHarmonicMetric (d : ℤ) (h : HermitianMetric B) (H : HolomorphicHiggsField B) : Prop :=
  0 < r ∧ ∀ i x, x ∈ B.core.baseSet i → ∀ u v,
    curvatureValue B (reconstructedConnection B h H.value) i x u v =
      centralCurvatureValue P d r x u v

def punctureMonodromy (d : ℤ) (r : ℕ) : Matrices r :=
  Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((d : ℂ) / (r : ℂ))) • (1 : Matrices r)

theorem rank_two_degree_one_monodromy : punctureMonodromy 1 2 = -(1 : Matrices 2) := by
  have h : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((1 : ℂ) / (2 : ℂ)) =
      (Real.pi : ℂ) * Complex.I := by ring
  simp only [punctureMonodromy, Int.cast_one, Nat.cast_ofNat]
  rw [h, Complex.exp_pi_mul_I]
  simp

end MathlibExt.AlgebraicGeometry.CentralCurvatureHarmonicBundles
