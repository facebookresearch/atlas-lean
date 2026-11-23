/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Mathlib source authors: Kim Morrison, Sina Hazratpour.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import Mathlib.CategoryTheory.Grothendieck

/-!
# Functors from a Grothendieck construction with explicit coherence

A family of fiber functors and coherent base-arrow transformations gives a
functor from the original Grothendieck category. Named public functor equalities
specify the identity and composition transports in the coherence types.
The object and arrow formulas are the ordinary Grothendieck construction.
-/

@[expose] public section

universe uC vC uF vF uE vE

set_option autoImplicit false

namespace CategoryTheory.Grothendieck

attribute [local simp] eqToHom_map

variable {C : Type uC} [Category.{vC} C] (F : C ⥤ Cat.{vF, uF})
  {E : Type uE} [Category.{vE} E]

/-- The identity base map has the same fiber functor, with its original source displayed. -/
theorem fiberFunctor_id_eq (fib : ∀ c, F.obj c ⥤ E) (c : C) :
    fib c = (F.map (𝟙 c)).toFunctor ⋙ fib c := by
  rw [F.map_id]
  rfl

/-- Two base maps give the actual composition transport of the target fiber functor. -/
theorem fiberFunctor_comp_eq (fib : ∀ c, F.obj c ⥤ E)
    {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) :
    (F.map f).toFunctor ⋙ ((F.map g).toFunctor ⋙ fib c₃) =
      (F.map (f ≫ g)).toFunctor ⋙ fib c₃ := by
  rw [F.map_comp]
  rfl

variable (fib : ∀ c, F.obj c ⥤ E)
  (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ (F.map f).toFunctor ⋙ fib c')
  (hom_id : ∀ c, hom (𝟙 c) = eqToHom (fiberFunctor_id_eq F fib c))
  (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃),
    hom (f ≫ g) = hom f ≫ Functor.whiskerLeft (F.map f).toFunctor (hom g) ≫
      eqToHom (fiberFunctor_comp_eq F fib f g))

set_option backward.isDefEq.respectTransparency.types false in
/-- Assemble the original fiber maps with public identity and composition coherences. -/
def functorFromWithCoherence : Grothendieck F ⥤ E where
  obj X := (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by simp [hom_id]
  map_comp f g := by simp [hom_comp]

/-- The assembled functor sends an original pair to its given fiber-functor image. -/
theorem functorFromWithCoherence_obj (X : Grothendieck F) :
    (functorFromWithCoherence F fib hom hom_id hom_comp).obj X =
      (fib X.base).obj X.fiber := rfl

/-- The assembled arrow is the original base transformation followed by the fiber arrow. -/
theorem functorFromWithCoherence_map {X Y : Grothendieck F} (f : X ⟶ Y) :
    (functorFromWithCoherence F fib hom hom_id hom_comp).map f =
      (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber := rfl

end CategoryTheory.Grothendieck
