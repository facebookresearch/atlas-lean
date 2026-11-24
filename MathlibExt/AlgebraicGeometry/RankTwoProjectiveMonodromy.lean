/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RankTwoHiggsAnalyticFrames
public import MathlibExt.AlgebraicGeometry.HarmonicReconstructionInterfaces
public import MathlibExt.AlgebraicGeometry.TwistedCharacterQuotientModels
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Degree-one central connections and actual punctured monodromy

The marking uses the actual fundamental groups of the curve and its
punctured complement. Smooth generator paths normalize the free basis
and the filled-surface relation. A degree-one reference line has its
actual evaluated algebraic frame transitions, Chern connection and
punctured nonzero section. Subtracting half its scalar connection form
from the central harmonic connection gives the punctured-flat matrix.

Parallel transports satisfy the actual local differential equation,
transition law and identity initial condition. Their endpoint matrices
fix every generator of an actual point of the twisted representation
scheme. The Betti class is the native invariant quotient of that point.

Source: Hitchin, The self-duality equations on a Riemann surface (1987),
Section 2, printed p67, and Section 9, printed pp110--112; dCHM,
arXiv:1004.1420v2, Introduction and Sections 1.2.1--1.2.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RankTwoProjectiveMonodromy

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry TopologicalSpace
open RankTwoHiggsCurveFamilies RankTwoHiggsAnalyticFrames ComplexAnalytification
open CoherentCurveLinearSeries KahlerClassGeometry SmoothHarmonicBundleGeometry
open CentralCurvatureHarmonicBundles HarmonicReconstructionInterfaces
open TwistedRankTwoRepresentations TwistedCharacterQuotientModels RankTwoMatrixGroupModels
open GeneralLinearFrameSchemes ManifoldDifferentialForms
open scoped Manifold ContDiff Matrix Matrix.Norms.Elementwise

variable (C : ComplexScheme) [AnalyticRealization.AnalyticManifold C 1] [IsProperCurve C.hom]
  [HasConstantGlobalSections C.hom]
  [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]

abbrev Punctured (puncture : space C) := {x : space C // x ≠ puncture}

structure SmoothPuncturedLoop (puncture : space C) (x : Punctured C puncture) where
  path : Path x x
  curve : ℝ → space C
  smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Coordinates 1) ∞ curve
  path_normalized : ∀ t : unitInterval, curve t = (path t).val

def loopClass {puncture : space C} {x : Punctured C puncture}
    (L : SmoothPuncturedLoop C puncture x) : FundamentalGroup (Punctured C puncture) x :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L.path)

def sourceWord {G : Type} [Group G] (g : ℕ) (a : Generators g → G) : G :=
  (List.finRange g).foldl (fun z i => z * (a (i, 0))⁻¹ * (a (i, 1))⁻¹ * a (i, 0) * a (i, 1)) 1

/-- Actual punctured generators and the kernel of filling in the puncture. -/
structure SurfaceMarking (puncture : space C) where
  basePoint : Punctured C puncture
  loops : Generators (genus C.hom) → SmoothPuncturedLoop C puncture basePoint
  free : FreeGroup (Generators (genus C.hom)) ≃* FundamentalGroup (Punctured C puncture) basePoint
  generators : ∀ i, free (FreeGroup.of i) = loopClass C (loops i)
  filledKernel :
    ((FundamentalGroup.map
      (show C(Punctured C puncture, space C) from ⟨Subtype.val, continuous_subtype_val⟩)
      basePoint).comp free.toMonoidHom).ker =
    Subgroup.normalClosure {sourceWord (genus C.hom) FreeGroup.of}

/-- A rank-one smooth atlas determined by the actual algebraic line coefficients. -/
structure LineFrames (L : C.left.Modules) where
  bundle : SmoothComplexBundle 1 (space C) 1
  holomorphic : ∀ i j, ContMDiffOn 𝓘(ℂ, Coordinates 1)
    𝓘(ℂ, FiberCoordinates 1 →L[ℂ] FiberCoordinates 1) ∞ (bundle.core.coordChange i j)
      (bundle.core.baseSet i ∩ bundle.core.baseSet j)
  chart : Fin bundle.count → C.left.Opens
  affine : ∀ i, IsAffineOpen (chart i)
  basis : ∀ i, Module.Basis (Fin 1) Γ(C.left, chart i) Γ(L, chart i)
  cover : ∀ x : C.left, ∃ i, x ∈ chart i
  membership : ∀ (i : Fin bundle.count) (x : ComplexPoints C.hom),
    x ∈ bundle.core.baseSet i ↔ x.Mem (chart i)
  regularFunctions : ∀ i (a : Γ(C.left, chart i)),
    ContMDiffOn 𝓘(ℂ, Coordinates 1) 𝓘(ℂ, ℂ) ∞ (regularEvaluation C (chart i) a)
      {p | p.Mem (chart i)}
  overlapBasis : ∀ i j, Module.Basis (Fin 1) Γ(C.left, chart i ⊓ chart j)
    Γ(L, chart i ⊓ chart j)
  overlap_normalized : ∀ i j a, overlapBasis i j a =
    (L.val.map (homOfLE (show chart i ⊓ chart j ≤ chart i from inf_le_left)).op).hom (basis i a)
  transition : ∀ i j (x : ComplexPoints C.hom) (hx : x.Mem (chart i ⊓ chart j)),
    transitionMatrix bundle i j x = fun a b => ComplexPoints.eval
      ((overlapBasis i j).repr
        ((L.val.map (homOfLE (show chart i ⊓ chart j ≤ chart j from inf_le_right)).op).hom
          (basis j b)) a) x hx

variable [ExteriorTheory ℝ (Coordinates 1) (space C)] (P : CurveNormalization (space C))

/-- The degree-one determinant reference, with its actual punctured trivialization. -/
structure ReferenceLine (puncture : space C) where
  module : C.left.Modules
  line : IsLineBundle module
  degree : degree C.hom module line = 1
  frames : LineFrames C module
  metric : HermitianMetric frames.bundle
  connection : SmoothConnection frames.bundle
  chern : connection.value = chernConnectionValue frames.bundle metric
  curvature : HasNormalizedCentralCurvature P frames.bundle 1 connection
  trivialization : Fin frames.bundle.count → space C → ℂ
  smooth : ∀ i, ContMDiffOn 𝓘(ℝ, Coordinates 1) 𝓘(ℝ, ℂ) ∞ (trivialization i)
    {x | x ∈ frames.bundle.core.baseSet i ∧ x ≠ puncture}
  nonzero : ∀ i x, x ∈ frames.bundle.core.baseSet i → x ≠ puncture → trivialization i x ≠ 0
  transition : ∀ i j x, x ∈ frames.bundle.core.baseSet i ∩ frames.bundle.core.baseSet j →
    x ≠ puncture →
      trivialization i x = transitionMatrix frames.bundle i j x 0 0 * trivialization j x

def referenceForm {puncture : space C} (R : ReferenceLine C P puncture)
    (x : space C) (u : Coordinates 1) : ℂ :=
  let i := R.frames.bundle.core.indexAt x
  (R.trivialization i x)⁻¹ *
    ((show ℂ from mfderivWithin 𝓘(ℝ, Coordinates 1) 𝓘(ℝ, ℂ) (R.trivialization i)
      {y | y ∈ R.frames.bundle.core.baseSet i ∧ y ≠ puncture} x u) +
      R.connection.matrix i x u 0 0 * R.trivialization i x)

def puncturedConnectionValue {puncture : space C} (R : ReferenceLine C P puncture)
    {E : GeometricHiggsFamilies.TwistedBundle C.left (canonicalLine C) 2}
    (V : AnalyticFrames C E) (A : SmoothConnection V.bundle) : OneFormValue V.bundle :=
  fun i x u => A.matrix i x u -
    ((1 / 2 : ℂ) * referenceForm C P R x u) • (1 : Matrices 2)

structure HarmonicSolution {puncture : space C} (R : ReferenceLine C P puncture)
    {E : GeometricHiggsFamilies.TwistedBundle C.left (canonicalLine C) 2}
    (V : AnalyticFrames C E) where
  metric : HermitianMetric V.bundle
  harmonic : IsCentralHarmonicMetric P V.bundle 1 metric V.higgs
  realization : ConnectionRealization V.bundle
    (reconstructedConnection V.bundle metric V.higgs.value)
  projective : HasNormalizedCentralCurvature P V.bundle 1 realization.connection
  puncturedFlat : ∀ i x, x ∈ V.bundle.core.baseSet i → x ≠ puncture → ∀ u v,
    curvatureValue V.bundle (puncturedConnectionValue C P R V realization.connection) i x u v = 0

def loopVelocity {puncture : space C} {x : Punctured C puncture}
    (L : SmoothPuncturedLoop C puncture x) (t : ℝ) : Coordinates 1 :=
  show Coordinates 1 from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Coordinates 1) L.curve t
    (show TangentSpace 𝓘(ℝ, ℝ) t from (1 : ℝ))

/-- Local fundamental solutions determine the actual framed transport endpoint. -/
structure ParallelTransport {puncture : space C} (R : ReferenceLine C P puncture)
    {E : GeometricHiggsFamilies.TwistedBundle C.left (canonicalLine C) 2}
    (V : AnalyticFrames C E) (A : HarmonicSolution C P R V)
    {x : Punctured C puncture} (L : SmoothPuncturedLoop C puncture x) where
  matrix : Fin V.bundle.count → ℝ → Matrices 2
  smooth : ∀ i, ContDiffOn ℝ ∞ (matrix i) {t | L.curve t ∈ V.bundle.core.baseSet i}
  transition : ∀ i j t, t ∈ Set.Icc (0 : ℝ) 1 →
    L.curve t ∈ V.bundle.core.baseSet i ∩ V.bundle.core.baseSet j →
      matrix i t = transitionMatrix V.bundle i j (L.curve t) * matrix j t
  initial : ∀ i, x.val ∈ V.bundle.core.baseSet i →
    matrix i 0 = transitionMatrix V.bundle i (V.bundle.core.indexAt x.val) x.val
  invertible : ∀ i t, t ∈ Set.Icc (0 : ℝ) 1 → L.curve t ∈ V.bundle.core.baseSet i →
    IsUnit (matrix i t)
  parallel : ∀ i t, t ∈ Set.Icc (0 : ℝ) 1 → L.curve t ∈ V.bundle.core.baseSet i →
    fderivWithin ℝ (matrix i) {t | L.curve t ∈ V.bundle.core.baseSet i} t 1 +
      puncturedConnectionValue C P R V A.realization.connection i (L.curve t)
        (loopVelocity C L t) * matrix i t = 0
  endpoint : Matrix.GeneralLinearGroup (Fin 2) ℂ
  normalized : (endpoint : Matrices 2) = matrix (V.bundle.core.indexAt x.val) 1

variable [FrameTheory 2] [GL2MatrixTheory]

/-- Every matrix generator is fixed by actual parallel transport, in the native scheme fibre. -/
structure SchemeMonodromy {puncture : space C} (R : ReferenceLine C P puncture)
    (T : SurfaceMarking C puncture)
    {E : GeometricHiggsFamilies.TwistedBundle C.left (canonicalLine C) 2}
    (V : AnalyticFrames C E) (A : HarmonicSolution C P R V) where
  transport : ∀ i, ParallelTransport C P R V A (T.loops i)
  point : ComplexPoints (representation (genus C.hom)).hom
  generators : ∀ i, GL2MatrixTheory.points (𝟙_ (Over (Spec (.of ℂ))))
    (pointMorphism point ≫ matrixGenerator (genus C.hom) i) =
      Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (.of ℂ)).inv.hom (transport i).endpoint

variable [Conjugation (genus C.hom)]

def monodromyClass {puncture : space C} {R : ReferenceLine C P puncture}
    {T : SurfaceMarking C puncture}
    {E : GeometricHiggsFamilies.TwistedBundle C.left (canonicalLine C) 2}
    {V : AnalyticFrames C E} {A : HarmonicSolution C P R V} (N : SchemeMonodromy C P R T V A) :
    space (bettiScheme (genus C.hom)) := spaceMap (quotientMap (genus C.hom)) N.point

end MathlibExt.AlgebraicGeometry.RankTwoProjectiveMonodromy
