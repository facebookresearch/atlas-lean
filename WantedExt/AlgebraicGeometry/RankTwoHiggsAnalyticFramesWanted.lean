/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RankTwoHiggsAnalyticFrames

/-!
# Actual algebraic and analytic rank-two Higgs fibre construction

These targets construct the pulled universal fibre and the smooth atlas
whose transitions and field are the actual algebraic coefficient evaluations.
They do not assume a harmonic metric or a nonabelian Hodge equivalence.
Source: Hitchin (1987), Sections 2 and 4; dCHM arXiv:1004.1420v2, Section 1.2.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RankTwoHiggsAnalyticFramesWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels RankTwoHiggsAnalyticFrames
open ComplexAnalytification KahlerClassGeometry
open scoped Manifold ContDiff

def_wanted nativeRankTwoHiggsPoint (C : ComplexScheme) [CurveSource C]
    (B : BaseChanges C) (M : ModuliModel C B) (p : ComplexPoints M.scheme.hom) :
    HiggsPointModel C M p

def_wanted nativeRankTwoHiggsAnalyticFrames (C : ComplexScheme) [CurveSource C]
    [AnalyticRealization.AnalyticManifold C 1]
    [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]
    [AnalyticRealization.RegularFunctions C 1]
    (E : GeometricHiggsFamilies.TwistedBundle C.left (canonicalLine C) 2) : AnalyticFrames C E

end WantedExt.AlgebraicGeometry.RankTwoHiggsAnalyticFramesWanted
