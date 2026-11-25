/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Opposites

/-!
# Opposite monads and comonads

The actual native opposite endofunctor takes a monad to a comonad, and a
comonad to a monad. Native structure morphisms reverse direction. The lawful
contravariant functors use these actual maps and require only a category.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Monad

/-- The opposite native endofunctor of a monad is a comonad. -/
def op (T : Monad C) : Comonad Cᵒᵖ where
  toFunctor := T.toFunctor.op
  ε := NatTrans.op T.η
  δ := NatTrans.op T.μ
  coassoc X := by
    change (T.μ.app X.unop).op ≫ (T.map (T.μ.app X.unop)).op =
      (T.μ.app X.unop).op ≫ (T.μ.app (T.obj X.unop)).op
    exact congrArg Quiver.Hom.op (T.assoc X.unop)
  left_counit X := by
    change (T.μ.app X.unop).op ≫ (T.η.app (T.obj X.unop)).op = 𝟙 _
    exact congrArg Quiver.Hom.op (T.left_unit X.unop)
  right_counit X := by
    change (T.μ.app X.unop).op ≫ (T.map (T.η.app X.unop)).op = 𝟙 _
    exact congrArg Quiver.Hom.op (T.right_unit X.unop)

/-- The opposite counit is the actual native unit with its direction reversed. -/
theorem op_ε_app (T : Monad C) (X : Cᵒᵖ) :
    (op T).ε.app X = (T.η.app X.unop).op := rfl

/-- The opposite comultiplication is the actual native multiplication reversed. -/
theorem op_δ_app (T : Monad C) (X : Cᵒᵖ) :
    (op T).δ.app X = (T.μ.app X.unop).op := rfl

end Monad

namespace Comonad

/-- The opposite native endofunctor of a comonad is a monad. -/
def op (G : Comonad C) : Monad Cᵒᵖ where
  toFunctor := G.toFunctor.op
  η := NatTrans.op G.ε
  μ := NatTrans.op G.δ
  assoc X := by
    change (G.map (G.δ.app X.unop)).op ≫ (G.δ.app X.unop).op =
      (G.δ.app (G.obj X.unop)).op ≫ (G.δ.app X.unop).op
    exact congrArg Quiver.Hom.op (G.coassoc X.unop)
  left_unit X := by
    change (G.ε.app (G.obj X.unop)).op ≫ (G.δ.app X.unop).op = 𝟙 _
    exact congrArg Quiver.Hom.op (G.left_counit X.unop)
  right_unit X := by
    change (G.map (G.ε.app X.unop)).op ≫ (G.δ.app X.unop).op = 𝟙 _
    exact congrArg Quiver.Hom.op (G.right_counit X.unop)

/-- The opposite unit is the actual native counit reversed. -/
theorem op_η_app (G : Comonad C) (X : Cᵒᵖ) :
    (op G).η.app X = (G.ε.app X.unop).op := rfl

/-- The opposite multiplication is the actual native comultiplication reversed. -/
theorem op_μ_app (G : Comonad C) (X : Cᵒᵖ) :
    (op G).μ.app X = (G.δ.app X.unop).op := rfl

end Comonad

namespace MonadHom

/-- A native monad morphism reverses to a native comonad morphism. -/
def op {S T : Monad C} (f : S ⟶ T) : Monad.op T ⟶ Monad.op S where
  toNatTrans := NatTrans.op f.toNatTrans
  app_ε X := by
    change (f.app X.unop).op ≫ (S.η.app X.unop).op = (T.η.app X.unop).op
    exact congrArg Quiver.Hom.op (f.app_η X.unop)
  app_δ X := by
    change (f.app X.unop).op ≫ (S.μ.app X.unop).op =
      (T.μ.app X.unop).op ≫ (f.app (T.obj X.unop)).op ≫
        (S.map (f.app X.unop)).op
    exact congrArg Quiver.Hom.op (f.app_μ X.unop)

end MonadHom

namespace ComonadHom

/-- A native comonad morphism reverses to a native monad morphism. -/
def op {S T : Comonad C} (f : S ⟶ T) : Comonad.op T ⟶ Comonad.op S where
  toNatTrans := NatTrans.op f.toNatTrans
  app_η X := by
    change (T.ε.app X.unop).op ≫ (f.app X.unop).op = (S.ε.app X.unop).op
    exact congrArg Quiver.Hom.op (f.app_ε X.unop)
  app_μ X := by
    change (T.δ.app X.unop).op ≫ (f.app X.unop).op =
      ((T.map (f.app X.unop)).op ≫ (f.app (S.obj X.unop)).op) ≫
        (S.δ.app X.unop).op
    exact congrArg Quiver.Hom.op (f.app_δ X.unop)

end ComonadHom

/-- Opposite native monads and actual reversed structure morphisms form a functor. -/
def Monad.opFunctor (C : Type u) [Category.{v} C] :
    (Monad C)ᵒᵖ ⥤ Comonad Cᵒᵖ where
  obj T := Monad.op T.unop
  map f := MonadHom.op f.unop
  map_id T := by
    apply ComonadHom.ext'
    funext X
    rfl
  map_comp f g := by
    apply ComonadHom.ext'
    funext X
    rfl

/-- Opposite native comonads and actual reversed structure morphisms form a functor. -/
def Comonad.opFunctor (C : Type u) [Category.{v} C] :
    (Comonad C)ᵒᵖ ⥤ Monad Cᵒᵖ where
  obj G := Comonad.op G.unop
  map f := ComonadHom.op f.unop
  map_id G := by
    apply MonadHom.ext'
    funext X
    rfl
  map_comp f g := by
    apply MonadHom.ext'
    funext X
    rfl

end CategoryTheory
