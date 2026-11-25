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
# The original double S-construction stages and exact functor maps

Iterate the actual finite-stage construction using its named genuine
Waldhausen structure. Both directions retain the original zero diagrams,
successive corner cofibrations, weak equivalences and pushouts. The
double-stage map is two applications of the actual original stage functor;
its exactness is earned twice from the original base functor.

These are categorical double stages. Spectrum structure maps and
delooping are subsequent obligations.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type uC) [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The actual outer S-stage of the original inner S-stage, with its
genuine named inner Waldhausen value. -/
def DoubleStage (m n : ℕ) : Type (max uC vC) :=
  letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  Stage (Stage C n) m

/-- The canonical double-stage zero-object structure is earned from
the original inner and outer zero diagrams. -/
theorem doubleStageHasZeroObject (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    HasZeroObject (Stage (Stage C n) m) := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  exact generalStageHasZeroObject (Stage C n) m

/-- The actual outer Waldhausen structure is built from the original
inner named value and the same original stage pushout construction. -/
@[instance_reducible]
def doubleStageWaldhausenCategory (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage (Stage C n) m) := doubleStageHasZeroObject C m n
    WaldhausenCategoryWithoutGluing (Stage (Stage C n) m) := by
  letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  letI : HasZeroObject (Stage (Stage C n) m) := doubleStageHasZeroObject C m n
  exact generalStageWaldhausenCategory (Stage C n) m

variable {C}
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- Two actual stage maps give the original double-stage functor. -/
def mapDoubleStage (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
    letI : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
    Stage (Stage C n) m ⥤ Stage (Stage D n) m := by
  letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  letI : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
  letI : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
  exact (hF.mapStage_isWaldhausenExact n).mapStage m

/-- The complete outer diagram is postcomposition by the original
inner stage functor. -/
theorem mapDoubleStage_obj (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
    letI : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
    ∀ A : Stage (Stage C n) m,
      ((mapDoubleStage hF m n).obj A).obj = A.obj ⋙ hF.mapStage n := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  let : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
  let : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
  intro A
  exact (hF.mapStage_isWaldhausenExact n).mapStage_obj m A

/-- The whole outer morphism is the original postwhiskered inner map. -/
theorem mapDoubleStage_map (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
    letI : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
    ∀ A B : Stage (Stage C n) m, ∀ f : A ⟶ B,
      ((mapDoubleStage hF m n).map f).hom = Functor.whiskerRight f.hom (hF.mapStage n) := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  let : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
  let : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
  intro A B f
  exact (hF.mapStage_isWaldhausenExact n).mapStage_map m f

/-- The full double-stage functor is exact for the actual named
Waldhausen values, without a stage-exactness assumption. -/
theorem mapDoubleStage_isWaldhausenExact (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
    letI : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
    letI : HasZeroObject (Stage (Stage C n) m) := generalStageHasZeroObject (Stage C n) m
    letI : WaldhausenCategoryWithoutGluing (Stage (Stage C n) m) :=
      generalStageWaldhausenCategory (Stage C n) m
    letI : HasZeroObject (Stage (Stage D n) m) := generalStageHasZeroObject (Stage D n) m
    letI : WaldhausenCategoryWithoutGluing (Stage (Stage D n) m) :=
      generalStageWaldhausenCategory (Stage D n) m
    (mapDoubleStage hF m n).IsWaldhausenExact := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  let : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
  let : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
  let : HasZeroObject (Stage (Stage C n) m) := generalStageHasZeroObject (Stage C n) m
  let : WaldhausenCategoryWithoutGluing (Stage (Stage C n) m) :=
    generalStageWaldhausenCategory (Stage C n) m
  let : HasZeroObject (Stage (Stage D n) m) := generalStageHasZeroObject (Stage D n) m
  let : WaldhausenCategoryWithoutGluing (Stage (Stage D n) m) :=
    generalStageWaldhausenCategory (Stage D n) m
  exact (hF.mapStage_isWaldhausenExact n).mapStage_isWaldhausenExact m

end CategoryTheory.Waldhausen.SConstruction
