/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AnalyticPeriodSourcesConstantInverseImageIso

/-!
# Integer constant inverse images

The integer constant inverse-image map has a two-sided inverse.

Sources: Scholze, arXiv:1205.3463v2, Definitions 3.9, 6.1, 6.8 and 8.1;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Section 5.1.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.AnalyticPeriodSourcesConstantInverseImageIso

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry AnalyticTateAdicModels AnalyticProEtaleCoefficientSources
open MathlibExt.CategoryTheory

example (p : ℕ) [Fact p.Prime] (X : AnalyticAdicSpace p)
    (hX hNoeth : AnalyticProObjectSites.IsLocallyNoetherian p X)
    (P : AnalyticProObjectSites.PointRealization p X)
    [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) CommRingCat.{1}]
    [HasSheafify (proTopology p X P) CommRingCat.{1}]
    [(etaleInclusion p X).IsContinuous
      (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)]
    [((etaleInclusion p X).sheafPushforwardContinuous CommRingCat.{1}
      (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)).IsRightAdjoint] :
    let f := NativeRingInverseImages.constantInverseMap
      (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (T := proTopology p X P)
      (etaleInclusion p X) ℤ
    ∃ g, f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := by
  have := WantedExt.AlgebraicGeometry.AnalyticPeriodSources.constantInverseImageIso
    p X hX P hNoeth ℤ
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

end MathlibExtTest.AlgebraicGeometry.AnalyticPeriodSourcesConstantInverseImageIso
