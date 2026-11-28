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
# Opposite monads, comonads, and structure morphisms

For a category C, reversing the arrows of a monad T gives a comonad on Cᵒᵖ: its counit is the
opposite of the unit and its comultiplication is the opposite of multiplication. Reversing a
comonad gives a monad by the dual formulas.

Structure morphisms reverse direction as well. These assignments define functors (Monad C)ᵒᵖ →
Comonad(Cᵒᵖ) and (Comonad C)ᵒᵖ → Monad(Cᵒᵖ), with independent object and morphism universes.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Monad

/-- Let T be a monad on a category C. Its opposite endofunctor on Cᵒᵖ is a comonad with counit
η^op and comultiplication μ^op. The monad unit and associativity equations become the comonad
counit and coassociativity equations under arrow reversal. -/
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

/-- For a monad T on C and X ∈ Cᵒᵖ, the counit of T.op at X equals (η_{X.unop})^op. Its direction
is T.op(X) → X. -/
theorem op_ε_app (T : Monad C) (X : Cᵒᵖ) :
    (op T).ε.app X = (T.η.app X.unop).op := rfl

/-- Let T be a monad on C and X ∈ Cᵒᵖ. The comultiplication of T.op at X is (μ_{X.unop})^op, a map
T.op(X) → T.op²(X). -/
theorem op_δ_app (T : Monad C) (X : Cᵒᵖ) :
    (op T).δ.app X = (T.μ.app X.unop).op := rfl

end Monad

namespace Comonad

/-- For a comonad G on C, the opposite endofunctor on Cᵒᵖ has monad unit ε^op and multiplication
δ^op. Reversing the comonad laws gives the monad laws. -/
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

/-- Let G be a comonad on C and X ∈ Cᵒᵖ. The unit of G.op at X equals (ε_{X.unop})^op : X →
G.op(X). -/
theorem op_η_app (G : Comonad C) (X : Cᵒᵖ) :
    (op G).η.app X = (G.ε.app X.unop).op := rfl

/-- For a comonad G on C and X ∈ Cᵒᵖ, the multiplication of G.op at X is (δ_{X.unop})^op :
G.op²(X) → G.op(X). -/
theorem op_μ_app (G : Comonad C) (X : Cᵒᵖ) :
    (op G).μ.app X = (G.δ.app X.unop).op := rfl

end Comonad

namespace MonadHom

/-- Let f : S → T be a monad morphism on C. Reversing its underlying natural transformation gives
a comonad morphism T.op → S.op on Cᵒᵖ. Its component at X is (f_{X.unop})^op and it preserves
the opposite counit and comultiplication. -/
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

/-- For a comonad morphism f : S → T on C, its opposite natural transformation defines a monad
morphism T.op → S.op on Cᵒᵖ, with component (f_{X.unop})^op. The structure equations are the
reversed comonad-morphism equations. -/
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

/-- Let C : Type u have morphism universe v. The assignment T ↦ T.op and f ↦ f.op gives a functor
(Monad C)ᵒᵖ → Comonad(Cᵒᵖ), preserving identities and composition with the reversed
directions. -/
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

/-- For a category C, taking opposite comonads and reversing their morphisms defines a functor
(Comonad C)ᵒᵖ → Monad(Cᵒᵖ). The object and morphism universes of C remain arbitrary. -/
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
