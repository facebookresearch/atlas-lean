/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RankTwoNonabelianHodgeModels

/-!
# Degree-one source-normalized NAH and native cohomology comparison

The target constructs a homeomorphism fixed by actual central harmonic
metrics, Chern connections and punctured parallel transport. Its Betti
map is the native pullback, whose bijectivity is requested independently.
For a fixed surface marking, changing the determinant reference leaves
this native cohomology identification unchanged.
Source: dCHM arXiv:1004.1420v2, Theorem 1.2.4 and (1.2.9); Hitchin (1987), Section 9.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RankTwoNonabelianHodgeModelsWanted

open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels RankTwoProjectiveMonodromy
open RankTwoNonabelianHodgeModels ComplexAnalytification KahlerClassGeometry
open ManifoldDifferentialForms CentralCurvatureHarmonicBundles GeneralLinearFrameSchemes
open RankTwoMatrixGroupModels TwistedRankTwoRepresentations TwistedCharacterQuotientModels
open scoped Manifold ContDiff

def_wanted nativeDegreeOneNAH (C : ComplexScheme) [CurveSource C]
    [AnalyticRealization.AnalyticManifold C 1]
    [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]
    [AnalyticRealization.RegularFunctions C 1]
    [ExteriorTheory ℝ (Coordinates 1) (space C)] [FrameTheory 2] [GL2MatrixTheory]
    [Conjugation (CoherentCurveLinearSeries.genus C.hom)]
    [CharacterQuotient (CoherentCurveLinearSeries.genus C.hom)]
    (B : BaseChanges C) (M : ModuliModel C B) (P : CurveNormalization (space C))
    (puncture : space C) (R : ReferenceLine C P puncture) (T : SurfaceMarking C puncture) :
    NAHModel C B M P puncture R T

theorem_wanted nativeDegreeOneNAHCohomology (C : ComplexScheme) [CurveSource C]
    [AnalyticRealization.AnalyticManifold C 1]
    [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]
    [ExteriorTheory ℝ (Coordinates 1) (space C)] [FrameTheory 2] [GL2MatrixTheory]
    [Conjugation (CoherentCurveLinearSeries.genus C.hom)]
    (B : BaseChanges C) (M : ModuliModel C B) (P : CurveNormalization (space C))
    (puncture : space C) (R : ReferenceLine C P puncture) (T : SurfaceMarking C puncture)
    (N : NAHModel C B M P puncture R T) (d : ℤ) :
    Function.Bijective (cohomologyMap C B M P puncture R T N d)

theorem_wanted nativeNAHReferenceIndependence (C : ComplexScheme) [CurveSource C]
    [AnalyticRealization.AnalyticManifold C 1]
    [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]
    [ExteriorTheory ℝ (Coordinates 1) (space C)] [FrameTheory 2] [GL2MatrixTheory]
    [Conjugation (CoherentCurveLinearSeries.genus C.hom)]
    (B : BaseChanges C) (M : ModuliModel C B) (P : CurveNormalization (space C))
    (puncture : space C) (R R' : ReferenceLine C P puncture) (T : SurfaceMarking C puncture)
    (N : NAHModel C B M P puncture R T) (N' : NAHModel C B M P puncture R' T) (d : ℤ) :
    cohomologyMap C B M P puncture R T N d = cohomologyMap C B M P puncture R' T N' d

end WantedExt.AlgebraicGeometry.RankTwoNonabelianHodgeModelsWanted
