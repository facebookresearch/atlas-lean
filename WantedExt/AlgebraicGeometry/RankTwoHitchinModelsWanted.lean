/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RankTwoHitchinModels

/-!
# Canonical-section bases and the actual Hitchin construction

The bases concern the native global-section modules. The Hitchin target
fixes the map on all stable families by their actual characteristic
polynomials, including native section and tensor-power comparisons.
Source: de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2, (1.3.1).
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RankTwoHitchinModelsWanted

open _root_.MathlibExt.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels RankTwoHitchinModels

def_wanted nativeCanonicalSectionBases (C : ComplexScheme) [CurveSource C] : SectionBases C

def_wanted nativeRankTwoHitchin (C : ComplexScheme) [CurveSource C]
    (B : BaseChanges C) (M : ModuliModel C B) (S : SectionBases C) : HitchinModel C B M S

end WantedExt.AlgebraicGeometry.RankTwoHitchinModelsWanted
