/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Presentable.FullSubcategory
import MathlibExt.CategoryTheory.Presentable.SurjectiveArrow

set_option autoImplicit false
noncomputable section

universe w u v

open CategoryTheory CategoryTheory.Presentable

section IndependentRank

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [P.ι.IsCardinalAccessible κ]

example (A : P.FullSubcategory) [IsCardinalPresentable A.obj κ] :
    IsCardinalPresentable A κ := P.isCardinalPresentable_of_ι κ A

end IndependentRank

attribute [local instance] Cardinal.fact_isRegular_aleph0

/- The actual point and fiber generators exercise the same-rank full-inclusion transfer. -/
example : IsCardinalPresentable pointArrow.{w} Cardinal.aleph0.{w} := inferInstance

example : IsCardinalPresentable relationArrow.{w} Cardinal.aleph0.{w} := inferInstance

example {A B : SurjectiveArrow.{w}} (f g : A ⟶ B) (h : f.hom.left = g.hom.left) :
    f = g := hom_ext_left f g h
