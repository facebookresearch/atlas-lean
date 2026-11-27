/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenExactFunctor

/-!
# Direct clients for the original exact S-stage maps

Source and target category universes are independent. Every genuine
stage pushout corner is mapped by the original functor.
-/

public section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.StageWaldhausenExactFunctor

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- The actual mapped stage retains every genuine source cofibration corner. -/
theorem originalStageCofibration (n : ℕ) {A B : Stage C n} (f : A ⟶ B)
    (hf : stageCofibrations C n f) :
    stageCofibrations D n ((hF.mapStage n).map f) :=
  hF.mapStage_cofibrations n f hf

/-- The whole mapped stage pushout is the image of the original supplied square. -/
theorem originalStagePushout (n : ℕ) {A B A' P : Stage C n}
    (i : A ⟶ B) (f : A ⟶ A') (inl : A' ⟶ P) (inr : B ⟶ P)
    (hi : stageCofibrations C n i) (hP : IsPushout f i inl inr) :
    IsPushout ((hF.mapStage n).map f) ((hF.mapStage n).map i)
      ((hF.mapStage n).map inl) ((hF.mapStage n).map inr) :=
  hF.mapStage_pushout n i f inl inr hi hP

/-- The exact stage maps use the canonical original named Waldhausen values. -/
theorem originalStageExactness (n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
    letI : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
    (hF.mapStage n).IsWaldhausenExact :=
  hF.mapStage_isWaldhausenExact n

end MathlibExtTest.StageWaldhausenExactFunctor
