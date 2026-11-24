/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenGeneral
public import MathlibExt.CategoryTheory.Waldhausen.Gluing

/-!
# Gluing for the original finite Waldhausen stages

The actual stage pushouts are pushouts in every original interval, and
actual stage cofibrations have cofibration components. Applying the base
gluing axiom in each original interval proves the gluing axiom for the
same original stage weak-equivalence property. No stage gluing witness
is supplied as an input.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Base gluing propagates to the actual finite stages with their original named structure. -/
theorem generalStageWaldhausenGluingAxiom (hGlue : WaldhausenGluingAxiom (C := C)) (n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    WaldhausenGluingAxiom (C := Stage C n) := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  constructor
  intro X Y Z P X' Y' Z' P' i f inY inZ i' f' inY' inZ' hP hP' x y z p
    hi hi' hix hfx hYP hZP hx hy hz
  have hi0 : stageCofibrations C n i :=
    (isCofibration_generalStageWaldhausenCategory_iff C n i).mp hi
  have hi0' : stageCofibrations C n i' :=
    (isCofibration_generalStageWaldhausenCategory_iff C n i').mp hi'
  apply (isWeakEquivalence_generalStageWaldhausenCategory_iff C n p).mpr
  rw [mem_stageWeak]
  intro a
  have hp0 := (GeneralStagePushoutPresentation.isPushout_app hi0 hP.flip a).flip
  have hp0' := (GeneralStagePushoutPresentation.isPushout_app hi0' hP'.flip a).flip
  exact hGlue.gluing hp0 hp0' (x.hom.app a) (y.hom.app a) (z.hom.app a) (p.hom.app a)
    (stageCofibrations_app C hi0 a) (stageCofibrations_app C hi0' a)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using
      congrArg (fun q : X ⟶ Y' => q.hom.app a) hix)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using
      congrArg (fun q : X ⟶ Z' => q.hom.app a) hfx)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using
      congrArg (fun q : Y ⟶ P' => q.hom.app a) hYP)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using
      congrArg (fun q : Z ⟶ P' => q.hom.app a) hZP)
    (((mem_stageWeak C n).mp
      ((isWeakEquivalence_generalStageWaldhausenCategory_iff C n x).mp hx)) a)
    (((mem_stageWeak C n).mp
      ((isWeakEquivalence_generalStageWaldhausenCategory_iff C n y).mp hy)) a)
    (((mem_stageWeak C n).mp
      ((isWeakEquivalence_generalStageWaldhausenCategory_iff C n z).mp hz)) a)

end CategoryTheory.Waldhausen.SConstruction
