/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatching

/-!
# Functorial relative matching arrows
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C]

@[no_expose]
noncomputable abbrev relativeMatchingObjectMap (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    relativeMatchingObject f.hom n ⟶
      relativeMatchingObject g.hom n :=
  pullback.map
    (matchingMap f.right n) ((matchingObjectFunctor n).map f.hom)
    (matchingMap g.right n) ((matchingObjectFunctor n).map g.hom)
    (q.right.app (op ⦋n⦌)) ((matchingObjectFunctor n).map q.left)
    ((matchingObjectFunctor n).map q.right)
    (matchingMap_naturality n q.right).symm
    (by
      simpa only [← Functor.map_comp] using
        (congrArg (fun h => (matchingObjectFunctor n).map h) q.w).symm)

set_option linter.defProp false in
@[reassoc, no_expose]
def relativeMatchingObjectMap_fst (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    relativeMatchingObjectMap n q ≫
        pullback.fst (matchingMap g.right n)
          ((matchingObjectFunctor n).map g.hom) =
      pullback.fst (matchingMap f.right n)
          ((matchingObjectFunctor n).map f.hom) ≫
        q.right.app (op ⦋n⦌) := by
  apply pullback.lift_fst

set_option linter.defProp false in
@[reassoc, no_expose]
def relativeMatchingObjectMap_snd (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    relativeMatchingObjectMap n q ≫
        pullback.snd (matchingMap g.right n)
          ((matchingObjectFunctor n).map g.hom) =
      pullback.snd (matchingMap f.right n)
          ((matchingObjectFunctor n).map f.hom) ≫
        (matchingObjectFunctor n).map q.left := by
  apply pullback.lift_snd

set_option backward.isDefEq.respectTransparency false in
set_option linter.defProp false in
@[no_expose]
def relativeMatchingMapArrowFunctor_w (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    q.left.app (op ⦋n⦌) ≫ relativeMatchingMap g.hom n =
      relativeMatchingMap f.hom n ≫ relativeMatchingObjectMap n q := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeMatchingMap_fst,
      Category.assoc, relativeMatchingObjectMap_fst,
      ← Category.assoc, relativeMatchingMap_fst]
    exact congrFun (congrArg NatTrans.app q.w) (op ⦋n⦌)
  · rw [Category.assoc, relativeMatchingMap_snd,
      Category.assoc, relativeMatchingObjectMap_snd,
      ← Category.assoc, relativeMatchingMap_snd]
    exact matchingMap_naturality n q.left

/-- Relative matching maps in degree `n` form a functor on arrows of simplicial objects. -/
noncomputable def relativeMatchingMapArrowFunctor (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    Arrow (SimplicialObject C) ⥤ Arrow C where
  obj f := Arrow.mk (relativeMatchingMap f.hom n)
  map q := Arrow.homMk (q.left.app (op ⦋n⦌))
    (relativeMatchingObjectMap n q) (relativeMatchingMapArrowFunctor_w n q)
  map_id f := by
    apply Arrow.hom_ext
    · rfl
    · change relativeMatchingObjectMap n (𝟙 f) = 𝟙 _
      apply pullback.hom_ext
      · rw [relativeMatchingObjectMap_fst]
        simp
      · rw [relativeMatchingObjectMap_snd]
        simp
  map_comp q r := by
    apply Arrow.hom_ext
    · rfl
    · change relativeMatchingObjectMap n (q ≫ r) =
        relativeMatchingObjectMap n q ≫ relativeMatchingObjectMap n r
      apply pullback.hom_ext
      · simp only [relativeMatchingObjectMap_fst, Arrow.comp_right,
          NatTrans.comp_app, Category.assoc]
        rw [relativeMatchingObjectMap_fst_assoc]
      · simp only [relativeMatchingObjectMap_snd, Arrow.comp_left,
          Functor.map_comp, Category.assoc]
        rw [relativeMatchingObjectMap_snd_assoc]

@[simp]
theorem relativeMatchingMapArrowFunctor_obj (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    (f : Arrow (SimplicialObject C)) :
    (relativeMatchingMapArrowFunctor n).obj f =
      Arrow.mk (relativeMatchingMap f.hom n) :=
  rfl

@[simp]
theorem relativeMatchingMapArrowFunctor_map_left (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    ((relativeMatchingMapArrowFunctor n).map q).left =
      q.left.app (op ⦋n⦌) :=
  rfl

@[reassoc (attr := simp)]
theorem relativeMatchingMapArrowFunctor_map_right_fst (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    ((relativeMatchingMapArrowFunctor n).map q).right ≫
        pullback.fst (matchingMap g.right n)
          ((matchingObjectFunctor n).map g.hom) =
      pullback.fst (matchingMap f.right n)
          ((matchingObjectFunctor n).map f.hom) ≫
        q.right.app (op ⦋n⦌) :=
  relativeMatchingObjectMap_fst n q

@[reassoc (attr := simp)]
theorem relativeMatchingMapArrowFunctor_map_right_snd (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    {f g : Arrow (SimplicialObject C)} (q : f ⟶ g) :
    ((relativeMatchingMapArrowFunctor n).map q).right ≫
        pullback.snd (matchingMap g.right n)
          ((matchingObjectFunctor n).map g.hom) =
      pullback.snd (matchingMap f.right n)
          ((matchingObjectFunctor n).map f.hom) ≫
        (matchingObjectFunctor n).map q.left :=
  relativeMatchingObjectMap_snd n q

end CategoryTheory.SimplicialObject
