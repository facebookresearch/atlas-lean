/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Limits.Comma

/-!
# Native presentability of the original source in a slice

An original κ-presentable source is κ-presentable as an object over any
fixed base. The underlying colimit factor already respects the base
triangle, because the colimit inclusions do. Equality is detected on the
same original underlying maps. The base requires no presentability or
cardinality bound; only the original working-universe colimits are used.
-/

universe w v u
open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]

/-- The same native κ-presentable source remains presentable with its specified whole base map. -/
theorem over_mk_isCardinalPresentable {A S : C} (f : A ⟶ S) (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalPresentable A κ] :
    IsCardinalPresentable (Over.mk f) κ := by
  apply IsCardinalPresentable.mk
  intro J _ _ F c hc
  let _ : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
  let U := F ⋙ Over.forget S
  let cU := (Over.forget S).mapCocone c
  have hcU : IsColimit cU := isColimitOfPreserves (Over.forget S) hc
  let _ : PreservesColimitsOfShape J (coyoneda.obj (op A)) :=
    preservesColimitsOfShape_of_isCardinalPresentable A κ J
  constructor
  · intro g
    let G : A ⟶ c.pt.left := g.left
    obtain ⟨j, a, ha⟩ := exists_hom_of_preservesColimit_coyoneda hcU G
    have ha' : a ≫ (c.ι.app j).left = G := ha
    let a' : Over.mk f ⟶ F.obj j := Over.homMk a (by
      change a ≫ (F.obj j).hom = f
      have hw : (c.ι.app j).left ≫ c.pt.hom = (F.obj j).hom := Over.w (c.ι.app j)
      exact (congrArg (fun t => a ≫ t) hw.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ c.pt.hom) ha').trans (Over.w g))))
    exact ⟨j, a', Over.OverMorphism.ext ha'⟩
  · intro j g h w
    let G : A ⟶ (F.obj j).left := g.left
    let H : A ⟶ (F.obj j).left := h.left
    have w' : G ≫ (c.ι.app j).left = H ≫ (c.ι.app j).left := congrArg Over.Hom.left w
    obtain ⟨k, a, ha⟩ := exists_eq_of_preservesColimit_coyoneda_self hcU G H w'
    exact ⟨k, a, Over.OverMorphism.ext ha⟩

end CategoryTheory
