/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

import MathlibExt.CategoryTheory.Enriched.FunctorCategory

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonoidalClosed

set_option autoImplicit false

noncomputable section

universe uA uV vV

section PlainEnrichedSource

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  (F G H : EnrichedFunctorCat V A) (a : F ⟶ G) (b : G ⟶ H)

-- The stored arrow carries full hom-object naturality without an ordinary source.
example : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    F.toEnrichedFunctor G.toEnrichedFunctor := a

example (X Y : A) :
    MonoidalClosed.uncurry (F.toEnrichedFunctor.map X Y) ≫
        EnrichedFunctorCat.component a Y =
      (EnrichedFunctorCat.component a X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry (G.toEnrichedFunctor.map X Y) :=
  a.uncurriedNaturality X Y

example (X : A) :
    EnrichedFunctorCat.component (a ≫ b) X =
      EnrichedFunctorCat.component a X ≫ EnrichedFunctorCat.component b X :=
  EnrichedFunctorCat.component_comp a b X

example (F₀ G₀ : EnrichedFunctor V A V)
    (q : ∀ X, F₀.obj X ⟶ G₀.obj X)
    (hq : ∀ X Y,
      MonoidalClosed.uncurry (F₀.map X Y) ≫ q Y =
        (q X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G₀.map X Y)) :
    (EnrichedFunctorCat.mk F₀) ⟶ (EnrichedFunctorCat.mk G₀) :=
  GradedNatTrans.unitOfComponents q hq

-- Importing the wrapper does not change Mathlib's category on the raw type.
example (F₀ G₀ : EnrichedFunctor V A V) (a₀ : EnrichedNatTrans F₀ G₀) :
    F₀ ⟶ G₀ := a₀

end PlainEnrichedSource

#print axioms CategoryTheory.EnrichedFunctorCat.category
#print axioms CategoryTheory.EnrichedFunctorCat.component_comp
#print axioms CategoryTheory.EnrichedFunctorCat.hom_ext
