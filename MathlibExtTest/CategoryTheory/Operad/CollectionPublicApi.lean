/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

import MathlibExt.CategoryTheory.Operad.Collection

/-!
# Focused O7E one-color collection public-contract packet

Pins the stable downstream-facing contracts for the finite-bijection
groupoid and one-color symmetric collections: hom/equiv conversion
with round-trip laws, identity/composition/reflexivity/transitivity
computations, evaluation at arities, and the relabel iso/equiv maps
with their hom projections and identity/composition laws.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v

variable {C : Type u} [Category.{v} C]

-- Hom-to-equiv conversion respects identities.
example (X : FinBijGroupoid) :
    FinBijGroupoid.equivOfHom (𝟙 X) = Equiv.refl _ :=
  FinBijGroupoid.equivOfHom_id X

-- Hom-to-equiv conversion respects composition.
example {X Y Z : FinBijGroupoid} (f : X ⟶ Y) (g : Y ⟶ Z) :
    FinBijGroupoid.equivOfHom (f ≫ g) =
      (FinBijGroupoid.equivOfHom f).trans
        (FinBijGroupoid.equivOfHom g) :=
  FinBijGroupoid.equivOfHom_comp f g

-- Hom-to-equiv conversion respects inverses.
example {X Y : FinBijGroupoid} (f : X ⟶ Y) :
    FinBijGroupoid.equivOfHom (Groupoid.inv f) =
      (FinBijGroupoid.equivOfHom f).symm :=
  FinBijGroupoid.equivOfHom_inv f

-- Equiv-to-hom conversion round-trips through hom-to-equiv.
example {X Y : FintypeCat} (e : X ≃ Y) :
    FinBijGroupoid.equivOfHom
        (FinBijGroupoid.homOfEquiv e) = e :=
  FinBijGroupoid.equivOfHom_homOfEquiv e

-- Equiv-to-hom sends reflexivity to identity.
example (X : FintypeCat) :
    FinBijGroupoid.homOfEquiv (Equiv.refl X) =
      𝟙 (⟨X⟩ : FinBijGroupoid) :=
  FinBijGroupoid.homOfEquiv_refl X

-- Equiv-to-hom respects transitivity.
example {X Y Z : FintypeCat} (e : X ≃ Y) (f : Y ≃ Z) :
    FinBijGroupoid.homOfEquiv (e.trans f) =
      FinBijGroupoid.homOfEquiv e ≫
        FinBijGroupoid.homOfEquiv f :=
  FinBijGroupoid.homOfEquiv_trans e f

-- Equiv-to-hom round-trips through hom-to-equiv.
example {X Y : FinBijGroupoid} (f : X ⟶ Y) :
    FinBijGroupoid.homOfEquiv
        (FinBijGroupoid.equivOfHom f) = f :=
  FinBijGroupoid.homOfEquiv_equivOfHom f

-- Evaluation at an arity is functor application.
example (X : SymmetricCollection C) (A : FintypeCat) :
    X.eval A = X.obj ⟨A⟩ :=
  rfl

-- Evaluation at `Fin n` unfolds through `FintypeCat.of`.
example (X : SymmetricCollection C) (n : ℕ) :
    X.evalFin n = X.eval (FintypeCat.of (Fin n)) :=
  rfl

-- The relabel iso projects to the relabel map.
example (X : SymmetricCollection C) {A B : FintypeCat}
    (i : A ≅ B) :
    (X.relabelIsoIso i).hom = X.relabelIso i :=
  X.relabelIsoIso_hom i

-- The relabel equiv iso projects to the relabel map.
example (X : SymmetricCollection C) {A B : FintypeCat}
    (e : A ≃ B) :
    (X.relabelEquivIso e).hom = X.relabelEquiv e :=
  X.relabelEquivIso_hom e

-- Relabeling along reflexivity is the identity.
example (X : SymmetricCollection C) (A : FintypeCat) :
    X.relabelIso (Iso.refl A) = 𝟙 (X.eval A) :=
  X.relabelIso_refl A

-- Relabeling along transitivity composes.
example (X : SymmetricCollection C) {A B C' : FintypeCat}
    (i : A ≅ B) (j : B ≅ C') :
    X.relabelIso (i ≪≫ j) =
      X.relabelIso i ≫ X.relabelIso j :=
  X.relabelIso_trans i j

-- Equiv relabeling along reflexivity is the identity.
example (X : SymmetricCollection C) (A : FintypeCat) :
    X.relabelEquiv (Equiv.refl A) = 𝟙 (X.eval A) :=
  X.relabelEquiv_refl A

-- Equiv relabeling along transitivity composes.
example (X : SymmetricCollection C) {A B C' : FintypeCat}
    (e : A ≃ B) (f : B ≃ C') :
    X.relabelEquiv (e.trans f) =
      X.relabelEquiv e ≫ X.relabelEquiv f :=
  X.relabelEquiv_trans e f
