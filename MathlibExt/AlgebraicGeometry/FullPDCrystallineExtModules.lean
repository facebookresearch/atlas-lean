/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FullPDCrystallineSheaves
public import MathlibExt.CategoryTheory.RingedSliceExtModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The fixed Ext module on the enlarged PD basis

The actual slice Ext presheaf and target-multiplication scalar action
are the same generic ringed-site construction used on the corrected
nilpotent basis. Native module sheafification fixes the full coefficient
module before finite-projectivity, crystal or evaluation is requested.
The change of basis requires its own normalized comparison theorem.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FullPDCrystallineExtModules

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open FullPDCrystallineTests FullPDCrystallineSheaves
open MathlibExt.CategoryTheory.RingedSliceExtModules

variable (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction)

/-- The underlying ring is this basis's original thickening-ring sheaf. -/
def coefficientRing : Sheaf (topology p A S) RingCat.{1} :=
  (sheafCompose (topology p A S) (forget₂ CommRingCat.{1} RingCat.{1})).obj
    (structureRingSheaf p A S)

/-- The original thickening rings map by their actual ring-sheafification unit. -/
def coefficientUnit : structureRingPresheaf p A S ⋙ forget₂ CommRingCat.{1} RingCat.{1} ⟶
    (coefficientRing p A S).obj :=
  Functor.whiskerRight
    ((sheafificationAdjunction (topology p A S) CommRingCat.{1}).unit.app
      (structureRingPresheaf p A S)) (forget₂ CommRingCat.{1} RingCat.{1})

variable (F : CoefficientSheaves p A S)

/-- The full slice Ext values retain their native restrictions and scalar multiplication. -/
def coefficientPresheaf (n : ℕ) :=
  _root_.MathlibExt.CategoryTheory.RingedSliceExtModules.localExtModulePresheaf
    (topology p A S) (structureRingSheaf p A S) F n

/-- Native module sheafification gives the fixed full-basis Ext module. -/
def coefficientModule (n : ℕ) : SheafOfModules.{1} (coefficientRing p A S) :=
  (PresheafOfModules.sheafification (𝟙 (coefficientRing p A S).obj)).obj
    (coefficientPresheaf p A S F n)

/-- Original local Ext classes enter by the same actual sheafification unit. -/
def localClassUnit (n : ℕ) : coefficientPresheaf p A S F n ⟶
    (coefficientModule p A S F n).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (coefficientRing p A S).obj)).unit.app (coefficientPresheaf p A S F n)

/-- The fixed module on each actual original PD ring, obtained through that same unit. -/
def nativeModule (n : ℕ) : PresheafOfModules.{1}
    (structureRingPresheaf p A S ⋙ forget₂ CommRingCat.{1} RingCat.{1}) :=
  (PresheafOfModules.restrictScalars (coefficientUnit p A S)).obj
    ((SheafOfModules.forget (coefficientRing p A S)).obj (coefficientModule p A S F n))

/-- The original semilinear map determines the full-basis tensor linearization. -/
def linearization (n : ℕ) {P Q : Obj p A S} (u : P ⟶ Q) :
    (ModuleCat.extendScalars.{1, 1, 1} ((structureRingPresheaf p A S).map u.op).hom).obj
      ((nativeModule p A S F n).obj (op Q)) ⟶
      (nativeModule p A S F n).obj (op P) :=
  ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1}
      ((structureRingPresheaf p A S).map u.op).hom).homEquiv
    ((nativeModule p A S F n).obj (op Q))
    ((nativeModule p A S F n).obj (op P))).symm ((nativeModule p A S F n).map u.op)

/-- Full-basis crystal properties refer to this exact constructed module and every original PD
map. -/
structure CrystalRealization where
  finite : ∀ P : Obj p A S,
    Module.Finite ((structureRingPresheaf p A S).obj (op P))
      ((nativeModule p A S F 1).obj (op P))
  projective : ∀ P : Obj p A S,
    Module.Projective ((structureRingPresheaf p A S).obj (op P))
      ((nativeModule p A S F 1).obj (op P))
  cartesian : ∀ {P Q : Obj p A S} (u : P ⟶ Q), IsIso (linearization p A S F 1 u)
  internalExt :
    (SheafOfModules.toSheaf (coefficientRing p A S)).obj (coefficientModule p A S F 1) ≅
      MathlibExt.CategoryTheory.SheafInternalExtModels.internalExt (topology p A S) F
        (structureSheaf p A S) 1

end MathlibExt.AlgebraicGeometry.FullPDCrystallineExtModules
