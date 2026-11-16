/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RankTwoHiggsModuliModels

/-!
# Native rank-two degree-one Higgs moduli construction request

The curve and every stable family are actual. The target constructs the
coarse moduli scheme and the coprime universal family, with full class-map
universality and actual pullback/base-line field comparisons.
Source: de Cataldo--Hausel--Migliorini arXiv:1004.1420v2,
Introduction and Section1.2.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.RankTwoHiggsModuliModelsWanted

open _root_.MathlibExt.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels

def_wanted nativeRankTwoDegreeOneHiggsModuli (C : ComplexScheme) [CurveSource C]
    (B : BaseChanges C) : ModuliModel C B

end WantedExt.AlgebraicGeometry.RankTwoHiggsModuliModelsWanted
