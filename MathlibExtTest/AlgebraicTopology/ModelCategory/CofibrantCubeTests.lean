/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube

/-!
# Cofibrant cube tests

These tests pin the pushout orientation, the minimal cofibrancy assumptions,
and the fact that the weak vertical map need not itself be a cofibration.
They install no left-properness or cobase-change instance.
-/

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.CofibrantCubeTests

open HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The canonical pushout-map theorem requires cofibrations only on the two
direct legs and explicit cofibrancy only at the common-source and non-direct
endpoints. -/
example {P₀ Q₀ R₀ P₁ Q₁ R₁ : C}
    (u₀ : P₀ ⟶ Q₀) (v₀ : P₀ ⟶ R₀)
    (u₁ : P₁ ⟶ Q₁) (v₁ : P₁ ⟶ R₁)
    (wP : P₀ ⟶ P₁) (wQ : Q₀ ⟶ Q₁) (wR : R₀ ⟶ R₁)
    (hu : u₀ ≫ wQ = wP ≫ u₁) (hv : v₀ ≫ wR = wP ≫ v₁)
    [Cofibration u₀] [Cofibration u₁]
    [WeakEquivalence wP] [WeakEquivalence wQ] [WeakEquivalence wR]
    [IsCofibrant P₀] [IsCofibrant P₁]
    [IsCofibrant R₀] [IsCofibrant R₁] :
    WeakEquivalence (pushout.map u₀ v₀ u₁ v₁ wQ wR wP hu hv) :=
  weakEquivalence_pushoutMap_of_cofibrant hu hv

/-- For two arbitrary pushout witnesses, the fourth vertical map has the
documented source-to-target orientation. -/
example {A B X P A' B' X' P' : C}
    {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
    {i' : A' ⟶ B'} {g' : A' ⟶ X'} {p' : B' ⟶ P'} {q' : X' ⟶ P'}
    (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
    {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
    (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
    (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')
    [Cofibration i] [Cofibration i']
    [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence c]
    [IsCofibrant A] [IsCofibrant A'] [IsCofibrant X] [IsCofibrant X'] :
    WeakEquivalence d :=
  weakEquivalence_map_of_isPushouts_of_cofibrant sq sq' hi hg hp hq

/-- Only the endpoints of the weak map are explicitly cofibrant. -/
example {A B X Y : C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j)
    [Cofibration i] [WeakEquivalence f]
    [IsCofibrant A] [IsCofibrant X] :
    WeakEquivalence f' :=
  weakEquivalence_of_isPushout_of_cofibrant sq

/-- With an identity weak leg, the induced right identity has the documented
orientation. -/
example {A B : C} (i : A ⟶ B) [Cofibration i] [IsCofibrant A] :
    WeakEquivalence (𝟙 B) := by
  exact weakEquivalence_of_isPushout_of_cofibrant
    (IsPushout.of_id_snd (f := i))

/-- With an identity cofibration, the induced map is the supplied weak map,
not the opposite pushout leg. -/
example {A X : C} (f : A ⟶ X)
    [WeakEquivalence f] [IsCofibrant A] [IsCofibrant X] :
    WeakEquivalence f := by
  exact weakEquivalence_of_isPushout_of_cofibrant
    (IsPushout.of_id_fst (f := f))

/-- The API does not require a cofibration instance on the weak leg. -/
example {A B X Y : C}
    (i : A ⟶ B) (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y)
    (sq : IsPushout i f f' j)
    [Cofibration i] [WeakEquivalence f]
    [IsCofibrant A] [IsCofibrant X] :
    WeakEquivalence f' := by
  exact weakEquivalence_of_isPushout_of_cofibrant sq

end MathlibExtTest.AlgebraicTopology.ModelCategory.CofibrantCubeTests
