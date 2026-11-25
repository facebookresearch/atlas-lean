/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeometricHitchinFiltrations
public import MathlibExt.AlgebraicGeometry.RankTwoNonabelianHodgeModels

/-!
# Independent geometric weight, actual Hitchin perverse filtration and P=W

The two image operators are already defined on the actual derived direct
images. The constructor/proof requests concern smooth proper SNC
compactification, constructibility, compactification independence and the
rank-two P=W theorem under the actual harmonic-monodromy NAH pullback.
Neither filtration equality nor an unrelated cohomology equivalence is an input.

Sources: Deligne, Theorie de Hodge II, Proposition 3.1.8 and Theorem 3.2.5;
dCHM arXiv:1004.1420v2, Section 1.4.1 and Theorem 1.1.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeometricHitchinFiltrationsWanted

open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels RankTwoHitchinModels
open RankTwoProjectiveMonodromy RankTwoNonabelianHodgeModels
open ComplexAnalytification PerverseSheaves BoundedBettiDirectImages GeometricHitchinFiltrations
open KahlerClassGeometry ManifoldDifferentialForms CentralCurvatureHarmonicBundles
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels
open TwistedRankTwoRepresentations TwistedCharacterQuotientModels
open scoped Manifold ContDiff

def_wanted nativeSNCCompactification (X : RankTwoHiggsCurveFamilies.ComplexScheme)
    [IsComplexVariety X]
    [Smooth X.hom] : SNCCompactification X

theorem_wanted nativeGeometricWeightIndependence (X : RankTwoHiggsCurveFamilies.ComplexScheme)
    [IsComplexVariety X]
    [Smooth X.hom] (J J' : SNCCompactification X)
    (A : BoundedDerivedAdjunction (spaceMap J.inclusion))
    (A' : BoundedDerivedAdjunction (spaceMap J'.inclusion)) (k d : ℤ) :
    weightFiltration J A k d = weightFiltration J' A' k d

theorem_wanted nativeHitchinDirectImageConstructible (C : RankTwoHiggsCurveFamilies.ComplexScheme)
    [CurveSource C]
    (B : BaseChanges C) (M : ModuliModel C B) (S : SectionBases C) (H : HitchinModel C B M S) :
    PerverseSheaves.boundedConstructible (base C) (shiftedHitchinComplex C B M S H)

theorem_wanted nativeRankTwoPerverseWeight (C : RankTwoHiggsCurveFamilies.ComplexScheme)
    [CurveSource C]
    [AnalyticRealization.AnalyticManifold C 1]
    [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]
    [ExteriorTheory ℝ (Coordinates 1) (space C)] [FrameTheory 2] [GL2MatrixTheory]
    [Conjugation (CoherentCurveLinearSeries.genus C.hom)]
    [CharacterQuotient (CoherentCurveLinearSeries.genus C.hom)]
    [IsComplexVariety (base C)] [PerverseSheafTheory (base C)]
    (B : BaseChanges C) (M : ModuliModel C B) (S : SectionBases C) (H : HitchinModel C B M S)
    (P : CurveNormalization (space C)) (puncture : space C)
    (R : ReferenceLine C P puncture) (T : SurfaceMarking C puncture)
    (N : NAHModel C B M P puncture R T)
    (J : SNCCompactification (bettiScheme (CoherentCurveLinearSeries.genus C.hom)))
    (Aχ : BoundedDerivedAdjunction (spaceMap H.map))
    (Aj : BoundedDerivedAdjunction (spaceMap J.inclusion))
    (h : PerverseSheaves.boundedConstructible (base C) (shiftedHitchinComplex C B M S H))
    (k d : ℤ) :
    (weightFiltration J Aj (2 * k) d).map (cohomologyMap C B M P puncture R T N d) =
      perverseFiltration C B M S H Aχ h k d ∧
    (weightFiltration J Aj (2 * k + 1) d).map (cohomologyMap C B M P puncture R T N d) =
      perverseFiltration C B M S H Aχ h k d

end WantedExt.AlgebraicGeometry.GeometricHitchinFiltrationsWanted
