/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Codomain retracts and arbitrary arrow retracts

Cobase change converts an arbitrary arrow retract into a codomain retract
whose source is held fixed. Therefore a morphism property closed under
cobase change and fixed-source codomain retracts is closed under all arrow
retracts.

This gives a native presentation of the codomain-retract clause in
Joyal–Tierney, arXiv math/0607820v2, the appendix's saturation definition.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

/-- Cobase change and literal fixed-source Under retracts imply closure
under arbitrary arrow retracts. -/
lemma isStableUnderRetracts_of_codomainRetracts
    {C : Type u} [Category.{v} C] [HasPushouts C]
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    (hcod : ∀ (X : C) (A B : Under X),
      Retract A B → P B.hom → P A.hom) :
    P.IsStableUnderRetracts where
  of_retract {X Y Z W f g} h hg := by
    let g' : X ⟶ pushout g h.r.left := pushout.inr g h.r.left
    have hg' : P g' := P.pushout_inr g h.r.left hg
    let i' : Under.mk f ⟶ Under.mk g' :=
      Under.homMk (h.i.right ≫ pushout.inl g h.r.left) (by
        dsimp [g']
        rw [← h.i_w_assoc, pushout.condition, h.retract_left_assoc]
        exact Category.id_comp _)
    let r' : Under.mk g' ⟶ Under.mk f :=
      Under.homMk (pushout.desc h.r.right f h.r_w.symm) (by
        dsimp [g']
        simp)
    have hr : Retract (Under.mk f) (Under.mk g') :=
      { i := i'
        r := r'
        retract := by
          ext
          dsimp [i', r']
          simp }
    exact hcod X _ _ hr hg'

end CategoryTheory.MorphismProperty
