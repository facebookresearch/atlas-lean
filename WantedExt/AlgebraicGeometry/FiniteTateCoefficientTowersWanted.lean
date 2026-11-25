/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FiniteTateCoefficientTowers
public import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

/-!
# All signed analytic Tate coefficient tower construction

Construction output preserves the actual reduction of finite coefficient
rings, u ↦ u^p on roots, all positive tensor maps, all negative enriched
dual evaluations and the sheafification units. No syntomic/nearby
equivalence is assumed while constructing these coefficient maps.

References: BMS19 arXiv:1802.03261v2, Theorem 10.1 and Remark 10.3;
BMS18 arXiv:1602.03148v3, Section 5.1; SGA4, Exposé IX.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.FiniteTateCoefficientTowers

open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticDiamondEtaleSites FormalNearbyCycleModels
open FiniteTateCoefficientTowers

public def_wanted analyticTateCoefficientTower (p : ℕ) [Fact p.Prime]
    (G : AnalyticAdicSpace p) (h : AnalyticProObjectSites.IsLocallyNoetherian p G) :
    TateTower p (analyticEtaleRings p G) (analyticEtaleTopology p G)

end WantedExt.AlgebraicGeometry.FiniteTateCoefficientTowers
