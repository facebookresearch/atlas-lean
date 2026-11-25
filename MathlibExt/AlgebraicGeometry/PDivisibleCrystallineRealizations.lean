/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDCrystallineExtSheafification
public import MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels

/-!
# Covariant crystalline realizations of the original p-divisible tower

The coefficient module is defined before its crystal properties:
sheafify the native slice Ext¹ of the actual Cartier dual and structure
sheaf, with original target multiplication as scalar action. The crystal
is required to have this exact coefficient presheaf, so an unrelated
module realization cannot replace the geometric Ext construction.

The internal-Ext comparison is a theorem/construction output between
these two fixed models; it does not define the underlying coefficient
module or its scalar action. General-base Cartier assembly and all F/V
and completed period evaluations have separate normalized interfaces.

Source: Scholze--Weinstein1211.6357v2, Sections3.2 and4.1;
Berthelot--Breen--Messing, Theorie de Dieudonne cristalline II.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleCrystallineRealizations

open _root_.CategoryTheory _root_.AlgebraicGeometry
open GeometricPDCrystallineTests GeometricPDCrystallineSheaves
open PDCrystallineExtSheafification PDivisibleGroupSchemes PDivisibleCartierTowerModels

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
  (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
  (A : PDBase) (f : Spec (.of R) ⟶ A.reduction)

/-- The actual scheme map to the divided-power reduction determines the crystalline base. -/
abbrev baseScheme := Over.mk f

/-- The covariant coefficient sheaf uses the actual original Cartier dual tower. -/
def dualCoefficientSheaf := groupSheaf p A (baseScheme R A f) D.group

/-- The fixed native covariant module is the original sheafified slice Ext¹. -/
def covariantModule : GeometricPDModuleCrystals.Modules p A (baseScheme R A f) :=
  nativeModule p A (baseScheme R A f) (dualCoefficientSheaf p R G D A f) 1

/-- The underlying fixed geometric Ext sheaf is retained separately. -/
def covariantInternalExt : CoefficientSheaves p A (baseScheme R A f) :=
  crystallineExt p A (baseScheme R A f) D.group

/-- Crystal existence and the internal-Ext comparison are properties of this exact source module. -/
structure Realization where
  crystal : GeometricPDModuleCrystals.Crystal p A (baseScheme R A f)
  module_eq : crystal.module = covariantModule p R G D A f
  internalExt : crystal.underlying ≅ covariantInternalExt p R G D A f

end MathlibExt.AlgebraicGeometry.PDivisibleCrystallineRealizations
