/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.DoubleStageReindex

public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.DoubleStageReindex

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Original operators in both directions commute for all simplex maps. -/
theorem originalDoubleInterchange {a b c d : SimplexCategory}
    (α : a ⟶ b) (β : c ⟶ d) :
    letI : HasZeroObject (Stage C c.len) := generalStageHasZeroObject C c.len
    letI : WaldhausenCategoryWithoutGluing (Stage C c.len) := generalStageWaldhausenCategory C c.len
    letI : HasZeroObject (Stage C d.len) := generalStageHasZeroObject C d.len
    letI : WaldhausenCategoryWithoutGluing (Stage C d.len) := generalStageWaldhausenCategory C d.len
    reindexDoubleStageOuter C α d.len ⋙ reindexDoubleStageInner C β a.len =
      reindexDoubleStageInner C β b.len ⋙ reindexDoubleStageOuter C α c.len :=
  reindexDoubleStage_interchange C α β

/-- Inner composition is the original contravariant operator composition. -/
theorem originalDoubleInnerComposition {a b c : SimplexCategory}
    (β : a ⟶ b) (γ : b ⟶ c) (m : ℕ) :
    letI : HasZeroObject (Stage C a.len) := generalStageHasZeroObject C a.len
    letI : WaldhausenCategoryWithoutGluing (Stage C a.len) := generalStageWaldhausenCategory C a.len
    letI : HasZeroObject (Stage C b.len) := generalStageHasZeroObject C b.len
    letI : WaldhausenCategoryWithoutGluing (Stage C b.len) := generalStageWaldhausenCategory C b.len
    letI : HasZeroObject (Stage C c.len) := generalStageHasZeroObject C c.len
    letI : WaldhausenCategoryWithoutGluing (Stage C c.len) := generalStageWaldhausenCategory C c.len
    reindexDoubleStageInner C (β ≫ γ) m =
      reindexDoubleStageInner C γ m ⋙ reindexDoubleStageInner C β m :=
  reindexDoubleStageInner_comp C β γ m

end MathlibExtTest.DoubleStageReindex
