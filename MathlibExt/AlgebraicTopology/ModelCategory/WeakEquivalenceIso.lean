/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory

/-!
# Canonical isomorphisms from weak equivalences

An explicit weak-equivalence proof determines the canonical isomorphism
induced by the model category's localization functor. Identity and
composition agree with the corresponding isomorphism operations.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra

/-- The canonical homotopy-category isomorphism induced by an explicit weak
equivalence. -/
noncomputable def weakEquivalenceIso
    {C : Type u} [Category.{v} C] [ModelCategory C]
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    ((weakEquivalences C).Q).obj X ≅ ((weakEquivalences C).Q).obj Y :=
  CategoryTheory.Localization.isoOfHom
    ((weakEquivalences C).Q) (weakEquivalences C) f hf

/-- The canonical isomorphism induced by an identity is the identity
isomorphism. -/
theorem weakEquivalenceIso_id
    {C : Type u} [Category.{v} C] [ModelCategory C] (X : C) :
    weakEquivalenceIso (𝟙 X) ((weakEquivalences C).id_mem X) =
      Iso.refl (((weakEquivalences C).Q).obj X) := by
  ext
  exact ((weakEquivalences C).Q).map_id X

/-- Canonical isomorphisms send source-first composition to transitivity of
isomorphisms. -/
theorem weakEquivalenceIso_comp
    {C : Type u} [Category.{v} C] [ModelCategory C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : weakEquivalences C f) (hg : weakEquivalences C g) :
    weakEquivalenceIso (f ≫ g)
        ((weakEquivalences C).comp_mem f g hf hg) =
      (weakEquivalenceIso f hf).trans (weakEquivalenceIso g hg) := by
  ext
  exact ((weakEquivalences C).Q).map_comp f g

end HomotopicalAlgebra
