/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monad.Opposite
public import MathlibExt.CategoryTheory.Monad.Bar
public import MathlibExt.CategoryTheory.Comonad.Cobar

/-!
# Opposite powers and insertion maps

The opposite comonad of a monad has the same iterated functor after unop.
The natural comparison transports counit and comultiplication insertions
to unit and multiplication insertions, preserving their source ordering.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.Monad

variable {C : Type u} [Category.{v} C]

/-- The actual opposite-comonad power has the native monad-power object after unop. -/
theorem monadPow_op_obj (T : Monad C) (n : ℕ) (X : C) :
    ((Comonad.comonadPow (Monad.op T) n).obj (Opposite.op X)).unop = (monadPow T n).obj X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
      change ((Comonad.comonadPow (Monad.op T) n).obj (Opposite.op (T.obj X))).unop =
        (monadPow T n).obj (T.obj X)
      exact ih (T.obj X)

/-- The object equality intertwines the actual iterated maps. -/
theorem monadPow_op_naturality (T : Monad C) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    ((Comonad.comonadPow (Monad.op T) n).map f.op).unop ≫
        eqToHom (monadPow_op_obj T n Y) =
      eqToHom (monadPow_op_obj T n X) ≫ (monadPow T n).map f := by
  induction n generalizing X Y with
  | zero =>
      change f ≫ 𝟙 _ = 𝟙 _ ≫ f
      rw [Category.comp_id, Category.id_comp]
  | succ n ih =>
      exact ih (T.map f)

/-- The natural comparison uses the actual native power functors and explicit object equalities. -/
def monadPowOpIso (T : Monad C) (n : ℕ) :
    (Comonad.comonadPow (Monad.op T) n).unop ≅ monadPow T n :=
  NatIso.ofComponents (fun X ↦ eqToIso (monadPow_op_obj T n X))
    (fun {_ _} f ↦ monadPow_op_naturality T n f)

/-- Opposite counit insertion is the actual native unit insertion in these coordinates. -/
theorem epsilonAtPos_op (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (X : C) :
    (Comonad.epsilonAtPos (Monad.op T) n i (Opposite.op X)).unop ≫
        (monadPowOpIso T (n + 1)).hom.app X =
      (monadPowOpIso T n).hom.app X ≫ etaAtPos T n i X := by
  induction n generalizing X with
  | zero =>
      change (T.η.app X) ≫ 𝟙 _ = 𝟙 _ ≫ (T.η.app X)
      rw [Category.comp_id, Category.id_comp]
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          change ((Comonad.comonadPow (Monad.op T) (n + 1)).map (T.η.app X).op).unop ≫
              (monadPowOpIso T (n + 1)).hom.app (T.obj X) =
            (monadPowOpIso T (n + 1)).hom.app X ≫
              (monadPow T (n + 1)).map (T.η.app X)
          exact (monadPowOpIso T (n + 1)).hom.naturality (T.η.app X)
      | succ i =>
          exact ih i (T.obj X)

/-- Opposite comultiplication insertion is the actual native multiplication insertion. -/
theorem deltaAtPos_op (T : Monad C) (n : ℕ) (i : Fin n) (X : C) :
    (Comonad.deltaAtPos (Monad.op T) n i (Opposite.op X)).unop ≫
        (monadPowOpIso T n).hom.app X =
      (monadPowOpIso T (n + 1)).hom.app X ≫ muAtPos T n i X := by
  induction n generalizing X with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          change ((Comonad.comonadPow (Monad.op T) n).map (T.μ.app X).op).unop ≫
              (monadPowOpIso T n).hom.app (T.obj X) =
            (monadPowOpIso T n).hom.app (T.obj (T.obj X)) ≫
              (monadPow T n).map (T.μ.app X)
          exact (monadPowOpIso T n).hom.naturality (T.μ.app X)
      | succ i =>
          exact ih i (T.obj X)

/-- The same public reversed positions identify source-ordered cofaces. -/
theorem cobarEpsilonAtPos_op (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (X : C) :
    (Comonad.cobarEpsilonAtPos (Monad.op T) n i (Opposite.op X)).unop ≫
        (monadPowOpIso T (n + 1)).hom.app X =
      (monadPowOpIso T n).hom.app X ≫ barEtaAtPos T n i X := by
  exact epsilonAtPos_op T n i.rev X

/-- The same public reversed positions identify source-ordered codegeneracies. -/
theorem cobarDeltaAtPos_op (T : Monad C) (n : ℕ) (i : Fin n) (X : C) :
    (Comonad.cobarDeltaAtPos (Monad.op T) n i (Opposite.op X)).unop ≫
        (monadPowOpIso T n).hom.app X =
      (monadPowOpIso T (n + 1)).hom.app X ≫ barMuAtPos T n i X := by
  exact deltaAtPos_op T n i.rev X

end CategoryTheory.Monad

end
