/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FullCrystallineRestrictionModels

/-!
# Full crystal extension and fixed Ext restriction comparison

This requests the actual full and nilpotent crystal realizations, their
native internal-Ext comparisons and the restriction comparison between
the independently fixed modules. None is a hypothesis of the request.

Source: BBM82; Scholze--Weinstein1211.6357v2, Section3.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.FullCrystallineRestriction

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
open MathlibExt.AlgebraicGeometry.FullCrystallineRestrictionModels

/-- Construct the full crystal, the nilpotent-basis crystal, and an isomorphism between the
restricted full-basis Ext module and the nilpotent-basis Ext module. -/
public def_wanted fullDieudonneCrystalExtension
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
    (A : MathlibExt.AlgebraicGeometry.FullPDCrystallineTests.PDBase)
    (s : Spec (.of R) ⟶ A.reduction) : ExtensionComparison p A R G D s

end WantedExt.AlgebraicGeometry.FullCrystallineRestriction
