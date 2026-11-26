/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.CategoryTheory.SmallObject.RelativeSourceSmallness

/-!# Same-source, same-chain uniform-smallness contracts -/
set_option autoImplicit false
noncomputable section
universe w u v
open CategoryTheory Limits MorphismProperty Opposite
open CategoryTheory.SmallObject

namespace MathlibExtTest.RelativeSourceSmallness

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  (h : UniformRelativeSourceSmallness.{w} P)

example (p : P.toSet) : Cardinal.{w} :=
  UniformRelativeSourceSmallness.sourceBound h p

example (p : P.toSet) (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hκ : UniformRelativeSourceSmallness.sourceBound h p < κ)
    (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F (coyoneda.obj (op p.1.left)) :=
  UniformRelativeSourceSmallness.sourceBound_spec h p κ hκ F hF

example (p : P.toSet) {β : Cardinal.{w}}
    (hβ : UniformRelativeSourceSmallness.sourceBound h p ≤ β)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType] (hκ : β < κ)
    (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F (coyoneda.obj (op p.1.left)) :=
  UniformRelativeSourceSmallness.sourceBound_mono h p hβ κ hκ F hF

example (p : P.toSet) (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hκ : UniformRelativeSourceSmallness.sourceBound h p < κ)
    (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j))))
    [HasColimit F] :
    IsColimit ((coyoneda.obj (op p.1.left)).mapCocone (colimit.cocone F)) :=
  UniformRelativeSourceSmallness.mappedCanonicalCocone h p κ hκ F hF

example (p : P.toSet) (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hκ : UniformRelativeSourceSmallness.sourceBound h p < κ)
    (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j))))
    [HasColimit F] (f : p.1.left ⟶ colimit F) :
    ∃ (j : κ.ord.ToType) (g : p.1.left ⟶ F.obj j), g ≫ colimit.ι F j = f :=
  UniformRelativeSourceSmallness.exists_stage_factor h p κ hκ F hF f

example (p : P.toSet) (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hκ : UniformRelativeSourceSmallness.sourceBound h p < κ)
    (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ j : κ.ord.ToType, ¬ IsMax j →
      relativeCellMaps.{w} P (F.map (homOfLE (Order.le_succ j))))
    [HasColimit F] {i j : κ.ord.ToType}
    (f : p.1.left ⟶ F.obj i) (g : p.1.left ⟶ F.obj j)
    (hfg : f ≫ colimit.ι F i = g ≫ colimit.ι F j) :
    ∃ (k : κ.ord.ToType) (a : i ⟶ k) (b : j ⟶ k), f ≫ F.map a = g ≫ F.map b :=
  UniformRelativeSourceSmallness.exists_stage_equality h p κ hκ F hF f g hfg

example {X Y : C} {f : X ⟶ Y}
    (c : HomotopicalAlgebra.AttachCells.{w} P.homFamily f) :
    relativeCellMaps.{w} P f :=
  attachCells_mem_relativeCellMaps P c

example (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {A B X Y : C} (i : A ⟶ B) (hi : P i)
    (hκ : UniformRelativeSourceSmallness.sourceBound h ⟨Arrow.mk i, hi⟩ < κ) (f : X ⟶ Y)
    (c : HomotopicalAlgebra.RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => P.homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (op A)) :=
  UniformRelativeSourceSmallness.preservesColimit_relativeCellComplex h κ i hi hκ f c

example (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {A B X Y : C} (i : A ⟶ B) (hi : P i)
    (hκ : UniformRelativeSourceSmallness.sourceBound h ⟨Arrow.mk i, hi⟩ < κ) (f : X ⟶ Y)
    (c : HomotopicalAlgebra.RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => P.homFamily) f) :
    IsColimit ((coyoneda.obj (op A)).mapCocone (Cocone.mk Y c.incl)) :=
  UniformRelativeSourceSmallness.relativeCellComplexMappedCocone h κ i hi hκ f c

end MathlibExtTest.RelativeSourceSmallness
