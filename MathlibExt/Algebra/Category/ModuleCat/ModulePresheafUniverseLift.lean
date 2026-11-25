/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# A universe lift of an entire module-presheaf diagram

Objects, actual semilinear restriction maps and their ring actions are
lifted together. This permits limits over a large source-chart category
without pretending that its diagram is small in the original coefficient
universe. The underlying source module can subsequently be recovered by
the native ULift linear equivalence.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift

open _root_.CategoryTheory _root_.Opposite

universe u v w
variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{0})

def obj (M : PresheafOfModules.{0} R) : PresheafOfModules.{w} R where
  obj X := ModuleCat.of (R.obj X) (ULift.{w} (M.obj X))
  map {X Y} f := by
    let target := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj Y) (ULift.{w} (M.obj Y)))
    letI : Module (R.obj X) (ULift.{w} (M.obj Y)) := target.isModule
    exact ModuleCat.ofHom
      { toFun := fun x => ULift.up ((M.map f).hom x.down)
        map_add' := by
          intro x y
          apply ULift.ext
          exact map_add (M.map f).hom x.down y.down
        map_smul' := by
          intro r x
          apply ULift.ext
          exact PresheafOfModules.map_smul M f r x.down }
  map_id X := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
    apply ULift.ext
    simp <;> rfl
  map_comp f g := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
    apply ULift.ext
    simp <;> rfl

def map {M N : PresheafOfModules.{0} R} (f : M ⟶ N) : obj R M ⟶ obj R N where
  app X := ModuleCat.ofHom
    { toFun := fun x => ULift.up ((f.app X).hom x.down)
      map_add' := by
        intro x y
        apply ULift.ext
        exact map_add (f.app X).hom x.down y.down
      map_smul' := by
        intro r x
        apply ULift.ext
        exact map_smul (f.app X).hom r x.down }
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    ext x
    apply ULift.ext
    change (f.app Y).hom (show M.obj Y from (M.map g).hom x.down) =
      (N.map g).hom ((f.app X).hom x.down)
    exact ConcreteCategory.congr_hom (f.naturality g) x.down

def functor : PresheafOfModules.{0} R ⥤ PresheafOfModules.{w} R where
  obj := obj R
  map f := map R f
  map_id M := by ext X x; rfl
  map_comp f g := by ext X x; rfl

instance : (functor R).Additive where
  map_add := by intros; ext X x; rfl

end MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift
