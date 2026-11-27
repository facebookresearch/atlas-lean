/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.DoubleStageCoherence
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageReindexWaldhausenExact

/-!
# Both original simplex directions of the double S-construction

The outer operator is original interval precomposition. The inner operator
is the original stage map of exact inner interval precomposition. General
stage exactness supplies every preservation field, and original stage
functoriality gives strict identity, composition and interchange.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The actual outer simplex operator on the original double stage. -/
def reindexDoubleStageOuter {a b : SimplexCategory} (α : a ⟶ b) (n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    Stage (Stage C n) b.len ⥤ Stage (Stage C n) a.len := by
  letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  exact reindexStage (C := Stage C n) α

/-- The actual inner simplex operator, mapped through the original outer stage. -/
def reindexDoubleStageInner {a b : SimplexCategory} (β : a ⟶ b) (m : ℕ) :
    letI : HasZeroObject (Stage C a.len) := generalStageHasZeroObject C a.len
    letI : WaldhausenCategoryWithoutGluing (Stage C a.len) := generalStageWaldhausenCategory C a.len
    letI : HasZeroObject (Stage C b.len) := generalStageHasZeroObject C b.len
    letI : WaldhausenCategoryWithoutGluing (Stage C b.len) := generalStageWaldhausenCategory C b.len
    Stage (Stage C b.len) m ⥤ Stage (Stage C a.len) m := by
  letI : HasZeroObject (Stage C a.len) := generalStageHasZeroObject C a.len
  letI : WaldhausenCategoryWithoutGluing (Stage C a.len) := generalStageWaldhausenCategory C a.len
  letI : HasZeroObject (Stage C b.len) := generalStageHasZeroObject C b.len
  letI : WaldhausenCategoryWithoutGluing (Stage C b.len) := generalStageWaldhausenCategory C b.len
  exact (reindexStage_general_isWaldhausenExact C β).mapStage m

/-- Both original directions commute before nerves or realization are taken. -/
theorem reindexDoubleStage_interchange {a b c d : SimplexCategory}
    (α : a ⟶ b) (β : c ⟶ d) :
    letI : HasZeroObject (Stage C c.len) := generalStageHasZeroObject C c.len
    letI : WaldhausenCategoryWithoutGluing (Stage C c.len) := generalStageWaldhausenCategory C c.len
    letI : HasZeroObject (Stage C d.len) := generalStageHasZeroObject C d.len
    letI : WaldhausenCategoryWithoutGluing (Stage C d.len) := generalStageWaldhausenCategory C d.len
    reindexDoubleStageOuter C α d.len ⋙ reindexDoubleStageInner C β a.len =
      reindexDoubleStageInner C β b.len ⋙ reindexDoubleStageOuter C α c.len := by
  let : HasZeroObject (Stage C c.len) := generalStageHasZeroObject C c.len
  let : WaldhausenCategoryWithoutGluing (Stage C c.len) := generalStageWaldhausenCategory C c.len
  let : HasZeroObject (Stage C d.len) := generalStageHasZeroObject C d.len
  let : WaldhausenCategoryWithoutGluing (Stage C d.len) := generalStageWaldhausenCategory C d.len
  exact (reindexStage_general_isWaldhausenExact C β).mapStage_reindex α

/-- The inner identity operator retains every original outer-stage value. -/
theorem reindexDoubleStageInner_id (a : SimplexCategory) (m : ℕ) :
    letI : HasZeroObject (Stage C a.len) := generalStageHasZeroObject C a.len
    letI : WaldhausenCategoryWithoutGluing (Stage C a.len) := generalStageWaldhausenCategory C a.len
    reindexDoubleStageInner C (𝟙 a) m = 𝟭 (Stage (Stage C a.len) m) := by
  rfl

/-- Source-first inner operators compose contravariantly on the same
original outer stage. -/
theorem reindexDoubleStageInner_comp {a b c : SimplexCategory}
    (β : a ⟶ b) (γ : b ⟶ c) (m : ℕ) :
    letI : HasZeroObject (Stage C a.len) := generalStageHasZeroObject C a.len
    letI : WaldhausenCategoryWithoutGluing (Stage C a.len) := generalStageWaldhausenCategory C a.len
    letI : HasZeroObject (Stage C b.len) := generalStageHasZeroObject C b.len
    letI : WaldhausenCategoryWithoutGluing (Stage C b.len) := generalStageWaldhausenCategory C b.len
    letI : HasZeroObject (Stage C c.len) := generalStageHasZeroObject C c.len
    letI : WaldhausenCategoryWithoutGluing (Stage C c.len) := generalStageWaldhausenCategory C c.len
    reindexDoubleStageInner C (β ≫ γ) m =
      reindexDoubleStageInner C γ m ⋙ reindexDoubleStageInner C β m := by
  rfl

/-- The original outer operator is Waldhausen exact on the actual double stage. -/
theorem reindexDoubleStageOuter_isWaldhausenExact {a b : SimplexCategory}
    (α : a ⟶ b) (n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage (Stage C n) a.len) := generalStageHasZeroObject (Stage C n) a.len
    letI : WaldhausenCategoryWithoutGluing (Stage (Stage C n) a.len) :=
      generalStageWaldhausenCategory (Stage C n) a.len
    letI : HasZeroObject (Stage (Stage C n) b.len) := generalStageHasZeroObject (Stage C n) b.len
    letI : WaldhausenCategoryWithoutGluing (Stage (Stage C n) b.len) :=
      generalStageWaldhausenCategory (Stage C n) b.len
    (reindexDoubleStageOuter C α n).IsWaldhausenExact := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  exact reindexStage_general_isWaldhausenExact (Stage C n) α

/-- The inner operator remains exact after application of the original outer stage. -/
theorem reindexDoubleStageInner_isWaldhausenExact {a b : SimplexCategory}
    (β : a ⟶ b) (m : ℕ) :
    letI : HasZeroObject (Stage C a.len) := generalStageHasZeroObject C a.len
    letI : WaldhausenCategoryWithoutGluing (Stage C a.len) := generalStageWaldhausenCategory C a.len
    letI : HasZeroObject (Stage C b.len) := generalStageHasZeroObject C b.len
    letI : WaldhausenCategoryWithoutGluing (Stage C b.len) := generalStageWaldhausenCategory C b.len
    letI : HasZeroObject (Stage (Stage C a.len) m) := generalStageHasZeroObject (Stage C a.len) m
    letI : WaldhausenCategoryWithoutGluing (Stage (Stage C a.len) m) :=
      generalStageWaldhausenCategory (Stage C a.len) m
    letI : HasZeroObject (Stage (Stage C b.len) m) := generalStageHasZeroObject (Stage C b.len) m
    letI : WaldhausenCategoryWithoutGluing (Stage (Stage C b.len) m) :=
      generalStageWaldhausenCategory (Stage C b.len) m
    (reindexDoubleStageInner C β m).IsWaldhausenExact := by
  let : HasZeroObject (Stage C a.len) := generalStageHasZeroObject C a.len
  let : WaldhausenCategoryWithoutGluing (Stage C a.len) := generalStageWaldhausenCategory C a.len
  let : HasZeroObject (Stage C b.len) := generalStageHasZeroObject C b.len
  let : WaldhausenCategoryWithoutGluing (Stage C b.len) := generalStageWaldhausenCategory C b.len
  exact (reindexStage_general_isWaldhausenExact C β).mapStage_isWaldhausenExact m

end CategoryTheory.Waldhausen.SConstruction
