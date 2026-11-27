/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageCanonicalZero

/-!
# Whole original zero-fold functor charts

The equality below retains the original exact functor on the original
source and target categories with independent universe roles.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction
open scoped ZeroObject

universe uC vC uD vD

variable {C : Type (max uC vC)} [Category.{vC} C] [HasZeroObject C]
    [WaldhausenCategoryWithoutGluing C]
variable {D : Type (max uD vD)} [Category.{vD} D] [HasZeroObject D]
    [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

example : mapIteratedStage hF [] ⋙ (iteratedStageNilEquivalence D).functor =
    (iteratedStageNilEquivalence C).functor ⋙ F :=
  mapIteratedStage_nil_chart hF

example : (iteratedStageNilEquivalence C).inverse.obj (0 : C) =
    (0 : IteratedStage C []) :=
  iteratedStageNilEquivalence_inverse_obj_zero C

example : iteratedStageCanonicalZero C [] = (0 : IteratedStage C []) :=
  iteratedStageCanonicalZero_nil_obj C

example : (iteratedStageNilEquivalence C).functor ⋙ (iteratedStageNilEquivalence C).inverse =
    𝟭 (IteratedStage C []) :=
  iteratedStageNilEquivalence_functor_inverse C

example : (iteratedStageNilEquivalence C).inverse ⋙ (iteratedStageNilEquivalence C).functor =
    𝟭 C :=
  iteratedStageNilEquivalence_inverse_functor C

end
