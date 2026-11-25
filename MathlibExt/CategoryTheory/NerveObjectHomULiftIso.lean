/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Category.ULift

/-!
# The full original nerve under independent object and Hom lifts

The canonical two source functors lift or lower every original object
and arrow. Both full chain directions identify their actual nerve with
the original coefficient-lifted nerve, for independent lift universes.
-/

@[expose] public section

noncomputable section

universe u v wo wh

open CategoryTheory Opposite
open scoped Simplicial

attribute [local instance] CategoryTheory.uliftCategory

namespace CategoryTheory

/-- Both original object and arrow directions retain all complete native chains under the
two independent canonical
lifts. -/
def nerveObjectHomULiftIso (C : Type u) [Category.{v} C] :
    SSet.uliftFunctor.{max u v wo wh,max u v}.obj (nerve C) ≅
      nerve (ULift.{wo} (ULiftHom.{wh} C)) :=
  NatIso.ofComponents (fun q =>
    ({ toFun := fun F =>
         ((ULiftHom.up.{v,u,wh} ⋙ ULift.upFunctor.{max v wh,u,wo}).mapComposableArrows
           q.unop.len).obj F.down
       invFun := fun F => ULift.up
         (((ULift.downFunctor.{max v wh,u,wo} ⋙
           ULiftHom.down.{v,u,wh}).mapComposableArrows q.unop.len).obj F)
       left_inv := fun F => by cases F; rfl
       right_inv := fun F => by
         apply Functor.ext (fun i => ULift.up_down (F.obj i)) } :
      ULift.{max u v wo wh} (ComposableArrows C q.unop.len) ≃
        ComposableArrows (ULift.{wo} (ULiftHom.{wh} C)) q.unop.len).toIso)
    (by intro q r θ; apply ConcreteCategory.hom_ext; intro F; rfl)

/-- Every same original chain reads the entire canonical object and Hom lift. -/
theorem nerveObjectHomULiftIso_hom_chain (C : Type u) [Category.{v} C]
    (q : SimplexCategoryᵒᵖ) (F : ComposableArrows C q.unop.len) :
    (nerveObjectHomULiftIso.{u,v,wo,wh} C).hom.app q (ULift.up F) =
      ((ULiftHom.up.{v,u,wh} ⋙ ULift.upFunctor.{max v wh,u,wo}).mapComposableArrows
        q.unop.len).obj F :=
  rfl

end CategoryTheory
