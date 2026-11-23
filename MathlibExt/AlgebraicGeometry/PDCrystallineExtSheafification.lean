/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves
public import MathlibExt.AlgebraicGeometry.GeometricPDModuleCrystals
public import MathlibExt.CategoryTheory.RingedSliceExtModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The fixed crystalline Ext coefficient module

The module is the native sheafification of the original slice-Ext
module presheaf: at a PD test `P` it is degree-`n` Ext from the restriction of `F` to the
restriction of the structure sheaf on the slice site over `P`, with restrictions given by the
exact slice pullbacks. This presheaf is the generic ringed-slice construction
`MathlibExt.CategoryTheory.RingedSliceExtModules.localExtModulePresheaf` on the nilpotent PD
site, the one also used on the full PD basis. Its coefficients already act by target
multiplication on actual derived Ext classes. Restriction to the actual thickening-ring
presheaf uses the original ring-sheafification unit. No module carrier or
scalar action is chosen by the later crystal realization request.

References: Stacks Project Tag01DH; Berthelot--Breen--Messing,
Theorie de Dieudonne cristalline II; Scholze--Weinstein1211.6357v2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDCrystallineExtSheafification

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open GeometricPDCrystallineTests GeometricPDCrystallineSheaves

variable (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction)

/-- The additive-module coefficient ring is the actual structure-ring sheaf. -/
def coefficientRing : Sheaf (topology p A S) RingCat.{1} :=
  (sheafCompose (topology p A S) (forget₂ CommRingCat.{1} RingCat.{1})).obj
    (structureRingSheaf p A S)

/-- The unit from the original thickening-ring presheaf to its actual sheafification. -/
def coefficientUnit : structureRingPresheaf p A S ⋙ forget₂ CommRingCat.{1} RingCat.{1} ⟶
    (coefficientRing p A S).obj :=
  Functor.whiskerRight
    ((sheafificationAdjunction (topology p A S) CommRingCat.{1}).unit.app
      (structureRingPresheaf p A S)) (forget₂ CommRingCat.{1} RingCat.{1})

variable (F : CoefficientSheaves p A S)

/-- The presheaf of local Ext modules over the structure ring: at a PD test `P`, degree-`n` Ext
from `F` to the structure sheaf on the slice site over `P`, acted on by target multiplication. -/
abbrev localExtModulePresheaf (n : ℕ) :=
  MathlibExt.CategoryTheory.RingedSliceExtModules.localExtModulePresheaf
    (topology p A S) (structureRingSheaf p A S) F n

/-- Native module sheafification of the original local Ext values and scalar action. -/
def moduleSheaf (n : ℕ) : SheafOfModules.{1} (coefficientRing p A S) :=
  (PresheafOfModules.sheafification (𝟙 (coefficientRing p A S).obj)).obj
    (localExtModulePresheaf p A S F n)

/-- The actual module on every original PD thickening ring, via that same unit. -/
def nativeModule (n : ℕ) : GeometricPDModuleCrystals.Modules p A S :=
  (PresheafOfModules.restrictScalars (coefficientUnit p A S)).obj
    ((SheafOfModules.forget (coefficientRing p A S)).obj (moduleSheaf p A S F n))

/-- The underlying additive sheaf has the same original sheafified local Ext sections. -/
def additiveSheaf (n : ℕ) : CoefficientSheaves p A S :=
  (SheafOfModules.toSheaf (coefficientRing p A S)).obj (moduleSheaf p A S F n)

omit [Fact p.Prime] in
/-- Restriction of coefficients changes no additive section or restriction map. -/
theorem nativeModule_isSheaf (n : ℕ) : Presheaf.IsSheaf (topology p A S)
    (nativeModule p A S F n).presheaf := by
  exact (additiveSheaf p A S F n).property

/-- The original local Ext class enters the fixed sheaf by the native module-sheafification unit. -/
def localClassUnit (n : ℕ) : localExtModulePresheaf p A S F n ⟶
    (moduleSheaf p A S F n).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (coefficientRing p A S).obj)).unit.app (localExtModulePresheaf p A S F n)

end MathlibExt.AlgebraicGeometry.PDCrystallineExtSheafification
