/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Presentable.CyclicPresheafSections

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Subfunctor Opposite

namespace MathlibExtTest.CyclicPresheafSections

variable {E : Type u} [SmallCategory E] {F : Eᵒᵖ ⥤ Type u} {a : E}

example (s : (yoneda.obj a).Elements) :
    (yonedaElementsArrow a s).left = s.obj.unop := rfl

example (s : (yoneda.obj a).Elements) :
    (yonedaElementsArrow a s).right = a := rfl

example (s : (yoneda.obj a).Elements) :
    (yonedaElementsArrow a s).hom = s.val := rfl

example : Function.Injective (yonedaElementsArrow a) := yonedaElementsArrow_injective a

example : Cardinal.mk (yoneda.obj a).Elements ≤ Cardinal.mk (Arrow E) :=
  mk_yoneda_elements_le_arrow a

example (x : F.obj (op a)) : yonedaToOfSection x ≫ (ofSection x).ι = yonedaEquiv.symm x :=
  yonedaToOfSection_comp_ι x

example (x : F.obj (op a)) : Epi (yonedaToOfSection x) := inferInstance

example (x : F.obj (op a)) (b : Eᵒᵖ) (f : b.unop ⟶ a) :
    ((yonedaToOfSection x).app b f).val = F.map f.op x :=
  yonedaToOfSection_app_val x b f

example (x : F.obj (op a)) : Function.Surjective (yonedaToOfSection x).mapElements.obj :=
  (yonedaToOfSection_elements x).1

example (x : F.obj (op a)) (s : (yoneda.obj a).Elements) :
    ((yonedaToOfSection x).mapElements.obj s).obj = s.obj ∧
      HEq (((yonedaToOfSection x).mapElements.obj s).val.val) (F.map s.val.op x) :=
  (yonedaToOfSection_elements x).2 s

example (x : F.obj (op a)) :
    Cardinal.mk (ofSection x).toFunctor.Elements ≤ Cardinal.mk (Arrow E) :=
  mk_elements_ofSection_le_arrow x

example (x : F.obj (op a)) (U : Subfunctor F) :
    let i := Arrow.mk (homOfLe (show U ⊓ ofSection x ≤ ofSection x from inf_le_right))
    Cardinal.mk i.left.Elements ≤ max Cardinal.aleph0 (Cardinal.mk (Arrow E)) ∧
      Cardinal.mk i.right.Elements ≤ max Cardinal.aleph0 (Cardinal.mk (Arrow E)) :=
  cyclicSectionArrow_bounds x U

end MathlibExtTest.CyclicPresheafSections
