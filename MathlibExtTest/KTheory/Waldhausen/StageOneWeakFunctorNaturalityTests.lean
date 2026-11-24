/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneWeakFunctorNaturality

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v uD vD
open CategoryTheory CategoryTheory.Limits
namespace MathlibExtTest.StageOneWeakFunctorNaturality
open CategoryTheory.Waldhausen.SConstruction
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- The entire original weak insertion square is naturally isomorphic under the original exact
functor. -/
def originalWeakSquare : stageOneGeneralWeak C ⋙ hF.mapStageWeak 1 ≅
    hF.mapWeakCategory ⋙ stageOneGeneralWeak D := stageOnePostcompWeakNatIso hF

end MathlibExtTest.StageOneWeakFunctorNaturality
