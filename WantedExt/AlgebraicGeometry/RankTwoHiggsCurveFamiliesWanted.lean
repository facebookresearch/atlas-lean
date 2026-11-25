/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RankTwoHiggsCurveFamilies

/-!
# Native degree-one Higgs-family reindexing construction request

The fixed curve is smooth, projective and connected with actual
cotangent line and genus at least2. The target reindexes actual stable
degree-one families and preserves their actual field and bundle arrows.
Source: de Cataldo--Hausel--Migliorini arXiv:1004.1420v2,
Introduction and Section1.2.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.RankTwoHiggsCurveFamiliesWanted

open _root_.MathlibExt.AlgebraicGeometry.RankTwoHiggsCurveFamilies

def_wanted nativeDegreeOneHiggsBaseChanges (C : ComplexScheme) [CurveSource C] : BaseChanges C

end WantedExt.AlgebraicGeometry.RankTwoHiggsCurveFamiliesWanted
