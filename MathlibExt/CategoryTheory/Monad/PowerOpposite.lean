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
# Powers and insertion maps under monad–comonad duality

Let T be a monad on C and G=T.op the opposite comonad. After unop, each power G^n has the same
object values as T^n, and these equalities give a natural power isomorphism.

Under this comparison, reversed counit insertions become unit insertions and reversed
comultiplication insertions become multiplication insertions. The same formulas hold for the
reversed-position cobar and bar conventions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.Monad

variable {C : Type u} [Category.{v} C]

/-- Let T be a monad on C, n ∈ ℕ, and X ∈ C. The object (T.op)^n(op X), after unop, equals T^n(X).
The powers are the comonadPow and monadPow constructions, including the identity at n=0. -/
theorem monadPow_op_obj (T : Monad C) (n : ℕ) (X : C) :
    ((Comonad.comonadPow (Monad.op T) n).obj (Opposite.op X)).unop = (monadPow T n).obj X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
      change ((Comonad.comonadPow (Monad.op T) n).obj (Opposite.op (T.obj X))).unop =
        (monadPow T n).obj (T.obj X)
      exact ih (T.obj X)

/-- For a monad T on C, n ∈ ℕ, and f : X → Y, the unop of the opposite-comonad power map f.op
followed by the object-equality map at Y equals the equality map at X followed by T^n(f). This
identifies both iterated maps in their monad-power coordinates. -/
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

/-- Let T be a monad on C and n ∈ ℕ. The object equalities ((T.op)^n(op X)).unop=T^n(X) give a
natural isomorphism between the unopped opposite-comonad power functor and monadPow T n. Its
components are the canonical isomorphisms of those equalities. -/
def monadPowOpIso (T : Monad C) (n : ℕ) :
    (Comonad.comonadPow (Monad.op T) n).unop ≅ monadPow T n :=
  NatIso.ofComponents (fun X ↦ eqToIso (monadPow_op_obj T n X))
    (fun {_ _} f ↦ monadPow_op_naturality T n f)

/-- Let T be a monad on C, e_n the forward map of its opposite-power comparison at X, n ∈ ℕ, i ∈
Fin(n+1), and X ∈ C. The unop of the counit insertion at position i followed by e_{n+1} equals
e_n followed by etaAtPos(T,n,i,X). The equality preserves the raw insertion position. -/
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

/-- For a monad T on C, n ∈ ℕ, i ∈ Fin n, and X ∈ C, let e_n be the forward map of the
opposite-power isomorphism at X. The unop of deltaAtPos(T.op,n,i,op X) followed by e_n equals
e_{n+1} followed by muAtPos(T,n,i,X). Both maps reduce n+1 monad factors to n. -/
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

/-- Let T be a monad on C, n ∈ ℕ, i ∈ Fin(n+1), and X ∈ C. Under the opposite-power isomorphisms
e, the unop of cobarEpsilonAtPos(T.op,n,i,op X) satisfies
ε_i.unop≫e_{n+1}=e_n≫barEtaAtPos(T,n,i,X). Both conventions use the reversed finite insertion
position. -/
theorem cobarEpsilonAtPos_op (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (X : C) :
    (Comonad.cobarEpsilonAtPos (Monad.op T) n i (Opposite.op X)).unop ≫
        (monadPowOpIso T (n + 1)).hom.app X =
      (monadPowOpIso T n).hom.app X ≫ barEtaAtPos T n i X := by
  exact epsilonAtPos_op T n i.rev X

/-- For a monad T on C, n ∈ ℕ, i ∈ Fin n, and X ∈ C, the unop of cobarDeltaAtPos(T.op,n,i,op X)
satisfies δ_i.unop≫e_n=e_{n+1}≫barMuAtPos(T,n,i,X). The isomorphisms e are the opposite-power
comparisons, and both insertions use the same reversed finite position. -/
theorem cobarDeltaAtPos_op (T : Monad C) (n : ℕ) (i : Fin n) (X : C) :
    (Comonad.cobarDeltaAtPos (Monad.op T) n i (Opposite.op X)).unop ≫
        (monadPowOpIso T n).hom.app X =
      (monadPowOpIso T (n + 1)).hom.app X ≫ barMuAtPos T n i X := by
  exact deltaAtPos_op T n i.rev X

end CategoryTheory.Monad

end
