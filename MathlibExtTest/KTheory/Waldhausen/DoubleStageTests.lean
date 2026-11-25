/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.DoubleStage

/-!
# Direct clients of the original double S-stages

The exact map and its entire object readout retain the original inner
functor with independent category universes.
-/

public section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.DoubleStage

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- Every outer object retains the full original inner functor map. -/
theorem originalDoubleObject (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
    letI : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
    ∀ A : Stage (Stage C n) m,
      ((mapDoubleStage hF m n).obj A).obj = A.obj ⋙ hF.mapStage n :=
  mapDoubleStage_obj hF m n

/-- The named double-stage zero value is an actual zero-object structure. -/
theorem originalDoubleZero (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    HasZeroObject (Stage (Stage C n) m) :=
  doubleStageHasZeroObject C m n

end MathlibExtTest.DoubleStage
