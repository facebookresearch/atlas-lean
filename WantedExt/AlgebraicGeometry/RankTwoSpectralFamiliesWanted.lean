/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RankTwoSpectralFamilies

/-!
# The native canonical-line spectral family construction

The target constructs the actual section-representing total K-space,
the ideal of the universal quadratic section and its full finite flat
double cover. Singular, reducible and nonreduced fibres are retained.
Source: de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2, (1.3.4)--(1.3.5).
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RankTwoSpectralFamiliesWanted

open _root_.MathlibExt.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHitchinModels RankTwoSpectralFamilies

def_wanted nativeRankTwoSpectralFamily (C : ComplexScheme) [CurveSource C]
    (S : SectionBases C) : SpectralFamily C S

end WantedExt.AlgebraicGeometry.RankTwoSpectralFamiliesWanted
