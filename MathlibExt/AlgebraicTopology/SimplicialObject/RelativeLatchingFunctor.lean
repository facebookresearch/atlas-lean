/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeLatching
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Functorial relative latching arrows
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C]

/-- Relative latching maps in degree `n` form a functor on arrows of simplicial objects. -/
noncomputable abbrev relativeLatchingMapArrowFunctor (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C] :
    Arrow (SimplicialObject C) ⥤ Arrow C :=
  ((evaluation (SimplicialObject C) C).flip.leibnizPushout).obj
    (Arrow.mk (latchingMapNatTrans (C := C) n))

@[simp]
theorem relativeLatchingMapArrowFunctor_obj (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    (f : Arrow (SimplicialObject C)) :
    (relativeLatchingMapArrowFunctor n).obj f =
      Arrow.mk (relativeLatchingMap f.hom n) :=
  rfl

@[simp]
theorem relativeLatchingMapArrowFunctor_map_right (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    ((relativeLatchingMapArrowFunctor n).map q).right =
      q.right.app (op ⦋n⦌) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem relativeLatchingMapArrowFunctor_map_left_inl (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    pushout.inl (latchingMap f.left n)
          ((latchingObjectFunctor n).map f.hom) ≫
        ((relativeLatchingMapArrowFunctor n).map q).left =
      q.left.app (op ⦋n⦌) ≫
        pushout.inl (latchingMap g.left n)
          ((latchingObjectFunctor n).map g.hom) :=
  by
    let F := (evaluation (SimplicialObject C) C).flip
    let l : Arrow (SimplicialObject C ⥤ C) :=
      Arrow.mk (latchingMapNatTrans (C := C) n)
    let sf : F.PushoutObjObj l.hom f.hom :=
      Functor.PushoutObjObj.ofHasPushout F l.hom f.hom
    let sg : F.PushoutObjObj l.hom g.hom :=
      Functor.PushoutObjObj.ofHasPushout F l.hom g.hom
    change sf.inl ≫ (sf.mapArrowRight sg q).left =
      q.left.app (op ⦋n⦌) ≫ sg.inl
    conv_lhs =>
      rhs
      change CommaMorphism.left (sf.mapArrowRight sg q)
      rw [Functor.PushoutObjObj.mapArrowRight_left sf sg q]
    apply sf.isPushout.inl_desc

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem relativeLatchingMapArrowFunctor_map_left_inr (n : ℕ)
    [HasColimitsOfShape (latchingIndex n) C]
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    pushout.inr (latchingMap f.left n)
          ((latchingObjectFunctor n).map f.hom) ≫
        ((relativeLatchingMapArrowFunctor n).map q).left =
      (latchingObjectFunctor n).map q.right ≫
        pushout.inr (latchingMap g.left n)
          ((latchingObjectFunctor n).map g.hom) :=
  by
    let F := (evaluation (SimplicialObject C) C).flip
    let l : Arrow (SimplicialObject C ⥤ C) :=
      Arrow.mk (latchingMapNatTrans (C := C) n)
    let sf : F.PushoutObjObj l.hom f.hom :=
      Functor.PushoutObjObj.ofHasPushout F l.hom f.hom
    let sg : F.PushoutObjObj l.hom g.hom :=
      Functor.PushoutObjObj.ofHasPushout F l.hom g.hom
    change sf.inr ≫ (sf.mapArrowRight sg q).left =
      (latchingObjectFunctor n).map q.right ≫ sg.inr
    conv_lhs =>
      rhs
      change CommaMorphism.left (sf.mapArrowRight sg q)
      rw [Functor.PushoutObjObj.mapArrowRight_left sf sg q]
    apply sf.isPushout.inr_desc

end CategoryTheory.SimplicialObject
