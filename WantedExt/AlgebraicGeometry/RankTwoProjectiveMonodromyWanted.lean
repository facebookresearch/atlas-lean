/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RankTwoProjectiveMonodromy

/-!
# Degree-one harmonic and twisted-monodromy construction requests

The connection is central rather than flat on the closed curve. The
punctured-flat correction uses the actual degree-one reference line.
All transport and matrix-point maps are fixed by their actual generators.
Source: Hitchin (1987), Sections 2,4,9; dCHM arXiv:1004.1420v2, Theorem 1.2.4.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RankTwoProjectiveMonodromyWanted

open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels RankTwoHiggsAnalyticFrames
open RankTwoProjectiveMonodromy ComplexAnalytification KahlerClassGeometry
open ManifoldDifferentialForms CentralCurvatureHarmonicBundles GeneralLinearFrameSchemes
open RankTwoMatrixGroupModels
open scoped Manifold ContDiff

def_wanted nativeSurfaceMarking (C : ComplexScheme) [CurveSource C]
    [AnalyticRealization.AnalyticManifold C 1]
    [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)] (puncture : space C) : SurfaceMarking C puncture

def_wanted nativeDegreeOneReferenceLine (C : ComplexScheme) [CurveSource C]
    [AnalyticRealization.AnalyticManifold C 1]
    [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]
    [AnalyticRealization.RegularFunctions C 1]
    [ExteriorTheory ℝ (Coordinates 1) (space C)]
    (P : CurveNormalization (space C)) (puncture : space C) : ReferenceLine C P puncture

def_wanted nativeDegreeOneHarmonicSolution (C : ComplexScheme) [CurveSource C]
    [AnalyticRealization.AnalyticManifold C 1]
    [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]
    [ExteriorTheory ℝ (Coordinates 1) (space C)]
    (P : CurveNormalization (space C)) (puncture : space C) (R : ReferenceLine C P puncture)
    (B : BaseChanges C) (M : ModuliModel C B) (p : ComplexPoints M.scheme.hom)
    (E : HiggsPointModel C M p) (V : AnalyticFrames C E.object) : HarmonicSolution C P R V

def_wanted nativeTwistedParallelMonodromy (C : ComplexScheme) [CurveSource C]
    [AnalyticRealization.AnalyticManifold C 1]
    [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]
    [ExteriorTheory ℝ (Coordinates 1) (space C)] [FrameTheory 2] [GL2MatrixTheory]
    (P : CurveNormalization (space C)) (puncture : space C) (R : ReferenceLine C P puncture)
    (T : SurfaceMarking C puncture)
    (E : GeometricHiggsFamilies.TwistedBundle C.left (canonicalLine C) 2)
    (V : AnalyticFrames C E) (A : HarmonicSolution C P R V) : SchemeMonodromy C P R T V A

end WantedExt.AlgebraicGeometry.RankTwoProjectiveMonodromyWanted
