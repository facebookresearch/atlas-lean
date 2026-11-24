/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FullPDCrystallineExtModules
public import MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels

/-!
# Dieudonne crystal on the enlarged p-nilpotent PD basis

The full-basis module is the actual sheafified local Ext of the original
Cartier dual, with its fixed target-multiplication action. Finite
projectivity, cartesian crystal maps and the native internal-Ext
comparison are outputs of this request. They are not inferred merely
from enlarging the nilpotent test category (nilpotent divided-power structures).

Source: BBM82; Scholze--Weinstein1211.6357v2, Section3.2 explicitly
extends Lie(E_G) beyond the nilpotent PD structure setting.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.FullPDivisibleCrystallineRealizations

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
open MathlibExt.AlgebraicGeometry.FullPDCrystallineTests
open MathlibExt.AlgebraicGeometry.FullPDCrystallineSheaves
open MathlibExt.AlgebraicGeometry.FullPDCrystallineExtModules

/-- Establish the full crystal and Ext comparison for this exact original dual coefficient sheaf. -/
public def_wanted fullCovariantDieudonneRealization
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
    (A : PDBase) (f : Spec (.of R) ⟶ A.reduction) :
    CrystalRealization p A (Over.mk f) (groupSheaf p A (Over.mk f) D.group)

end WantedExt.AlgebraicGeometry.FullPDivisibleCrystallineRealizations
