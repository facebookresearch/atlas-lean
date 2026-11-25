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
# Original double-stage identity and composition

Two applications of the original stage functor preserve exact-functor
identity and composition. These laws retain the actual inner and outer
stage diagrams, without replacing the categorical double S-construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD uE vE

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {E : Type uE} [Category.{vE} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]

private theorem stageMap_eq_of_functor_eq {F G : C ⥤ D}
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (h : F = G) (n : ℕ) :
    hF.mapStage n = hG.mapStage n := by
  subst G
  rfl

/-- The original double stage of the identity is the actual identity
functor at both stage directions. -/
theorem mapDoubleStage_id (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    mapDoubleStage (Functor.IsWaldhausenExact.id (C := C)) m n =
      𝟭 (Stage (Stage C n) m) := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  have hInner := Functor.IsWaldhausenExact.mapStage_id (C := C) n
  unfold mapDoubleStage
  exact (stageMap_eq_of_functor_eq
    ((Functor.IsWaldhausenExact.id (C := C)).mapStage_isWaldhausenExact n)
    (Functor.IsWaldhausenExact.id (C := Stage C n)) hInner m).trans
      (Functor.IsWaldhausenExact.mapStage_id (C := Stage C n) m)

variable {F : C ⥤ D} {G : D ⥤ E}

/-- Composing original exact functors gives the composition of their
actual double-stage maps in both original directions. -/
theorem mapDoubleStage_comp (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
    letI : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
    letI : HasZeroObject (Stage E n) := generalStageHasZeroObject E n
    letI : WaldhausenCategoryWithoutGluing (Stage E n) := generalStageWaldhausenCategory E n
    mapDoubleStage (hF.comp hG) m n = mapDoubleStage hF m n ⋙ mapDoubleStage hG m n := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  let : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
  let : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
  let : HasZeroObject (Stage E n) := generalStageHasZeroObject E n
  let : WaldhausenCategoryWithoutGluing (Stage E n) := generalStageWaldhausenCategory E n
  have hInner := Functor.IsWaldhausenExact.mapStage_comp hF hG n
  unfold mapDoubleStage
  exact (stageMap_eq_of_functor_eq ((hF.comp hG).mapStage_isWaldhausenExact n)
    ((hF.mapStage_isWaldhausenExact n).comp (hG.mapStage_isWaldhausenExact n)) hInner m).trans
      (Functor.IsWaldhausenExact.mapStage_comp
        (hF.mapStage_isWaldhausenExact n) (hG.mapStage_isWaldhausenExact n) m)

end CategoryTheory.Waldhausen.SConstruction
