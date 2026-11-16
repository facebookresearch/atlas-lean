/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PDivisibleCrystallineRealizations

/-!
# Crystal properties of the original covariant Ext module

This request supplies the finite-projective crystal and comparison
with native internal Ext. The coefficient module and its scalar
multiplication are already fixed by actual slice Ext/sheafification.
Source: Scholze--Weinstein1211.6357v2, Sections3.2/4.1; BBM82.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PDivisibleCrystallineRealizations

open _root_.AlgebraicGeometry _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
open MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests
open MathlibExt.AlgebraicGeometry.PDivisibleCrystallineRealizations

/-- Prove crystal properties and the internal-Ext comparison for this fixed original coefficient
module. -/
public def_wanted covariantDieudonneRealization
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
    (A : PDBase) (f : Spec (.of R) ⟶ A.reduction) : Realization p R G D A f

end WantedExt.AlgebraicGeometry.PDivisibleCrystallineRealizations
