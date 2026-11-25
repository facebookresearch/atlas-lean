/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.KahlerClassGeometry
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Complex.Order

/-!
# Actual smooth Hermitian and harmonic bundle geometry

The bundle is constructed by the native VectorBundleCore. Matrices refer
to its actual finite atlas and coordinate-change maps. A metric consists
of smooth positive definite Hermitian matrices with the exact transition
law. The connection, adjoint connection, unitary/self-adjoint decomposition,
type projections and curvature are literal differential/matrix formulas.

Sources: Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, section 2, printed pages 9–11. Native bundle/calculus
constructions: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Topology/VectorBundle/Basic.lean (Nicolò Cavalleri, Sébastien Gouëzel,
Heather Macbeth, Patrick Massot, Floris van Doorn),
Geometry/Manifold/VectorBundle/Basic.lean (Floris van Doorn, Heather Macbeth),
LinearAlgebra/Matrix/PosDef.lean (Alexander Bentkamp, Mohanad Ahmed), and
Analysis/Matrix/Normed.lean (Heather Macbeth, Eric Wieser), Apache 2.0.
No existence of a metric,
flat connection, or nonabelian-Hodge correspondence is assumed.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry

open _root_.CategoryTheory TopologicalSpace Set
open KahlerClassGeometry ManifoldDifferentialForms
open scoped Manifold ContDiff Matrix BigOperators ComplexOrder Matrix.Norms.Elementwise

abbrev FiberCoordinates (r : ℕ) := Fin r → ℂ
abbrev Matrices (r : ℕ) := Matrix (Fin r) (Fin r) ℂ

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]

structure SmoothComplexBundle (r : ℕ) where
  count : ℕ
  core : VectorBundleCore ℂ M (FiberCoordinates r) (Fin count)
  smooth : ∀ i j, ContMDiffOn 𝓘(ℝ, Coordinates n)
    𝓘(ℝ, FiberCoordinates r →L[ℂ] FiberCoordinates r) ∞ (core.coordChange i j)
      (core.baseSet i ∩ core.baseSet j)

variable {n M} {r : ℕ} (B : SmoothComplexBundle n M r)

def frameOpen (i : Fin B.count) : Opens M := ⟨B.core.baseSet i, B.core.isOpen_baseSet i⟩

/-- The matrix sends j-frame coordinates to i-frame coordinates. -/
def transitionMatrix (i j : Fin B.count) (x : M) : Matrices r :=
  LinearMap.toMatrix (Pi.basisFun ℂ (Fin r)) (Pi.basisFun ℂ (Fin r))
    (B.core.coordChange j i x).toLinearMap

def matrixDifferential (i : Fin B.count) (H : M → Matrices r) (x : M)
    (u : Coordinates n) : Matrices r :=
  mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Matrices r) H (B.core.baseSet i) x u

structure HermitianMetric where
  matrix : Fin B.count → M → Matrices r
  smooth : ∀ i, ContMDiffOn 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Matrices r) ∞ (matrix i)
    (B.core.baseSet i)
  positive : ∀ i x, x ∈ B.core.baseSet i → (matrix i x).PosDef
  transition : ∀ i j x, x ∈ B.core.baseSet i ∩ B.core.baseSet j →
    matrix j x = (transitionMatrix B i j x)ᴴ * matrix i x * transitionMatrix B i j x

def frameMetricValue (h : HermitianMetric B) (i : Fin B.count) (x : M)
    (v w : FiberCoordinates r) : ℂ := star v ⬝ᵥ ((h.matrix i x) *ᵥ w)

omit [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
theorem frameMetricValue_positive (h : HermitianMetric B) (i : Fin B.count) (x : M)
    (hx : x ∈ B.core.baseSet i) (v : FiberCoordinates r) (hv : v ≠ 0) :
    0 < frameMetricValue B h i x v v := (h.positive i x hx).dotProduct_mulVec_pos hv

def metricValue (h : HermitianMetric B) (x : M) (v w : B.core.Fiber x) : ℂ :=
  let i := B.core.indexAt x
  frameMetricValue B h i x ((B.core.localTriv i) ⟨x, v⟩).2
    ((B.core.localTriv i) ⟨x, w⟩).2

def chartConnectionMatrix (P : Fin B.count → M → Coordinates n →L[ℝ] Matrices r)
    (i : Fin B.count) (a : M) (z : Coordinates n) : Coordinates n →L[ℝ] Matrices r := by
  classical
  exact if hz : z ∈ chartDomain ℝ (Coordinates n) M (frameOpen B i) a then
    (P i ((extChartAt 𝓘(ℝ, Coordinates n) a).symm z)).comp
      (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) a).symm z)
  else 0

structure SmoothConnection where
  matrix : Fin B.count → M → Coordinates n →L[ℝ] Matrices r
  smooth : ∀ i a, ContDiffOn ℝ ∞ (chartConnectionMatrix B matrix i a)
    (chartDomain ℝ (Coordinates n) M (frameOpen B i) a)
  transition : ∀ i j x, x ∈ B.core.baseSet i ∩ B.core.baseSet j → ∀ u : Coordinates n,
    matrix j x u = (transitionMatrix B i j x)⁻¹ * matrix i x u * transitionMatrix B i j x +
      (transitionMatrix B i j x)⁻¹ * (show Matrices r from
        mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Matrices r) (transitionMatrix B i j)
          (B.core.baseSet i ∩ B.core.baseSet j) x u)

abbrev OneFormValue := Fin B.count → M → Coordinates n → Matrices r

def SmoothConnection.value (A : SmoothConnection B) : OneFormValue B := fun i x u ↦ A.matrix i x u

def chartOneFormValue (A : OneFormValue B) (i : Fin B.count) (a : M)
    (z u : Coordinates n) : Matrices r := by
  classical
  exact
  if hz : z ∈ chartDomain ℝ (Coordinates n) M (frameOpen B i) a then
    A i ((extChartAt 𝓘(ℝ, Coordinates n) a).symm z)
      (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
        (extChartAt 𝓘(ℝ, Coordinates n) a).symm z u)
  else 0

/-- The actual chart pullback derivative of a matrix one-form. -/
def exteriorOneForm (A : OneFormValue B) (i : Fin B.count) (x : M)
    (u v : Coordinates n) : Matrices r :=
  let z := extChartAt 𝓘(ℝ, Coordinates n) x x
  let du := mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
    (extChartAt 𝓘(ℝ, Coordinates n) x) x u
  let dv := mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n)
    (extChartAt 𝓘(ℝ, Coordinates n) x) x v
  fderivWithin ℝ (fun y ↦ chartOneFormValue B A i x y dv)
      (chartDomain ℝ (Coordinates n) M (frameOpen B i) x) z du -
    fderivWithin ℝ (fun y ↦ chartOneFormValue B A i x y du)
      (chartDomain ℝ (Coordinates n) M (frameOpen B i) x) z dv

def curvatureValue (A : OneFormValue B) (i : Fin B.count) (x : M)
    (u v : Coordinates n) : Matrices r :=
  exteriorOneForm B A i x u v + A i x u * A i x v - A i x v * A i x u

def IsFlat (A : SmoothConnection B) : Prop :=
  ∀ i x, x ∈ B.core.baseSet i → ∀ u v, curvatureValue B A.value i x u v = 0

def typeOneZero (A : OneFormValue B) : OneFormValue B := fun i x u ↦
  (1 / 2 : ℂ) • (A i x u - Complex.I • A i x (Complex.I • u))

def typeZeroOne (A : OneFormValue B) : OneFormValue B := fun i x u ↦
  (1 / 2 : ℂ) • (A i x u + Complex.I • A i x (Complex.I • u))

/-- The literal metric adjoint connection d+h⁻¹dh-h⁻¹Aᴴh. -/
def adjointConnection (h : HermitianMetric B) (A : SmoothConnection B) : OneFormValue B :=
  fun i x u ↦ (h.matrix i x)⁻¹ * matrixDifferential B i (h.matrix i) x u -
    (h.matrix i x)⁻¹ * (A.matrix i x u)ᴴ * h.matrix i x

def unitaryPart (h : HermitianMetric B) (A : SmoothConnection B) : OneFormValue B :=
  fun i x u ↦ (1 / 2 : ℂ) • (A.matrix i x u + adjointConnection B h A i x u)

def selfAdjointPart (h : HermitianMetric B) (A : SmoothConnection B) : OneFormValue B :=
  fun i x u ↦ (1 / 2 : ℂ) • (A.matrix i x u - adjointConnection B h A i x u)

def extractedTheta (h : HermitianMetric B) (A : SmoothConnection B) : OneFormValue B :=
  typeOneZero B (selfAdjointPart B h A)

def extractedBarConnection (h : HermitianMetric B) (A : SmoothConnection B) : OneFormValue B :=
  typeZeroOne B (unitaryPart B h A)

def covariantExterior (A theta : OneFormValue B) (i : Fin B.count) (x : M)
    (u v : Coordinates n) : Matrices r :=
  exteriorOneForm B theta i x u v + A i x u * theta i x v - A i x v * theta i x u +
    theta i x u * A i x v - theta i x v * A i x u

def typeZeroTwo (F : Coordinates n → Coordinates n → Matrices r)
    (u v : Coordinates n) : Matrices r :=
  (1 / 4 : ℂ) • (F u v + Complex.I • F (Complex.I • u) v +
    Complex.I • F u (Complex.I • v) - F (Complex.I • u) (Complex.I • v))

def typeOneOne (F : Coordinates n → Coordinates n → Matrices r)
    (u v : Coordinates n) : Matrices r :=
  (1 / 2 : ℂ) • (F u v + F (Complex.I • u) (Complex.I • v))

/-- These are the three actual equations in Simpson section 2: bar-part
integrability, bar(theta)=0 and theta wedge theta=0. -/
def IsPluriharmonic (h : HermitianMetric B) (A : SmoothConnection B) : Prop :=
  ∀ i x, x ∈ B.core.baseSet i → ∀ u v : Coordinates n,
    typeZeroTwo (curvatureValue B (unitaryPart B h A) i x) u v = 0 ∧
    typeOneOne (covariantExterior B (unitaryPart B h A) (extractedTheta B h A) i x) u v = 0 ∧
    extractedTheta B h A i x u * extractedTheta B h A i x v -
      extractedTheta B h A i x v * extractedTheta B h A i x u = 0

def chernConnectionValue (h : HermitianMetric B) : OneFormValue B := fun i x u ↦
  (h.matrix i x)⁻¹ * typeOneZero B
    (fun j y v ↦ matrixDifferential B j (h.matrix j) y v) i x u

def thetaAdjoint (h : HermitianMetric B) (theta : OneFormValue B) : OneFormValue B :=
  fun i x u ↦ (h.matrix i x)⁻¹ * (theta i x u)ᴴ * h.matrix i x

def reconstructedConnection (h : HermitianMetric B) (theta : OneFormValue B) : OneFormValue B :=
  fun i x u ↦ chernConnectionValue B h i x u + theta i x u + thetaAdjoint B h theta i x u

def holomorphicChartTheta (theta : Fin B.count → M → Coordinates n →L[ℂ] Matrices r)
    (i : Fin B.count) (a : M) (z : Coordinates n) : Coordinates n →L[ℂ] Matrices r := by
  classical
  exact if hz : z ∈ chartDomain ℂ (Coordinates n) M (frameOpen B i) a then
    (theta i ((extChartAt 𝓘(ℂ, Coordinates n) a).symm z)).comp
      (mfderiv 𝓘(ℂ, Coordinates n) 𝓘(ℂ, Coordinates n)
        (extChartAt 𝓘(ℂ, Coordinates n) a).symm z)
  else 0

structure HolomorphicHiggsField where
  holomorphicBundle : ∀ i j, ContMDiffOn 𝓘(ℂ, Coordinates n)
    𝓘(ℂ, FiberCoordinates r →L[ℂ] FiberCoordinates r) ∞ (B.core.coordChange i j)
      (B.core.baseSet i ∩ B.core.baseSet j)
  theta : Fin B.count → M → Coordinates n →L[ℂ] Matrices r
  holomorphic : ∀ i a, ContDiffOn ℂ ∞ (holomorphicChartTheta B theta i a)
    (chartDomain ℂ (Coordinates n) M (frameOpen B i) a)
  transition : ∀ i j x, x ∈ B.core.baseSet i ∩ B.core.baseSet j → ∀ u : Coordinates n,
    theta j x u = (transitionMatrix B i j x)⁻¹ * theta i x u * transitionMatrix B i j x
  integrable : ∀ i x, x ∈ B.core.baseSet i → ∀ u v : Coordinates n,
    theta i x u * theta i x v - theta i x v * theta i x u = 0

def HolomorphicHiggsField.value (H : HolomorphicHiggsField B) : OneFormValue B :=
  fun i x u ↦ H.theta i x u

def IsHarmonicMetric (h : HermitianMetric B) (H : HolomorphicHiggsField B) : Prop :=
  ∀ i x, x ∈ B.core.baseSet i → ∀ u v,
    curvatureValue B (reconstructedConnection B h H.value) i x u v = 0

def lambdaConnectionValue (h : HermitianMetric B) (H : HolomorphicHiggsField B)
    (lambda : ℂ) : OneFormValue B :=
  fun i x u ↦ lambda • chernConnectionValue B h i x u + HolomorphicHiggsField.value B H i x u

def lambdaBarValue (h : HermitianMetric B) (H : HolomorphicHiggsField B)
    (lambda : ℂ) : OneFormValue B := fun i x u ↦ lambda • thetaAdjoint B h H.value i x u

omit [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
@[simp] theorem lambda_zero (h : HermitianMetric B) (H : HolomorphicHiggsField B) :
    lambdaConnectionValue B h H 0 = H.value := by
  funext i x u
  simp [lambdaConnectionValue]

omit [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
@[simp] theorem lambda_bar_zero (h : HermitianMetric B) (H : HolomorphicHiggsField B) :
    lambdaBarValue B h H 0 = 0 := by
  funext i x u
  simp [lambdaBarValue]

omit [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
theorem lambda_one (h : HermitianMetric B) (H : HolomorphicHiggsField B) :
    (fun i x u ↦ lambdaConnectionValue B h H 1 i x u + lambdaBarValue B h H 1 i x u) =
      reconstructedConnection B h H.value := by
  funext i x u
  simp [lambdaConnectionValue, lambdaBarValue, reconstructedConnection]

end MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
