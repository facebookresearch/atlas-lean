/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.ModelCategory.WeakEquivalenceIso

/-!
# Tests for canonical weak-equivalence isomorphisms
-/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.MorphismProperty
open HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

example {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalenceIso f hf =
      Localization.isoOfHom
        ((weakEquivalences C).Q) (weakEquivalences C) f hf :=
  rfl

example {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    (weakEquivalenceIso f hf).hom = ((weakEquivalences C).Q).map f :=
  rfl

example {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    ((weakEquivalences C).Q).map f ≫ (weakEquivalenceIso f hf).inv = 𝟙 _ := by
  simpa only [weakEquivalenceIso] using
    Localization.isoOfHom_hom_inv_id
      ((weakEquivalences C).Q) (weakEquivalences C) f hf

example {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    (weakEquivalenceIso f hf).inv ≫ ((weakEquivalences C).Q).map f = 𝟙 _ := by
  simpa only [weakEquivalenceIso] using
    Localization.isoOfHom_inv_hom_id
      ((weakEquivalences C).Q) (weakEquivalences C) f hf

example (X : C) :
    (weakEquivalenceIso (𝟙 X) ((weakEquivalences C).id_mem X)).inv = 𝟙 _ := by
  simpa only [weakEquivalenceIso] using
    Localization.isoOfHom_id_inv
      ((weakEquivalences C).Q) (weakEquivalences C) X
        ((weakEquivalences C).id_mem X)

example (X : C) :
    weakEquivalenceIso (𝟙 X) ((weakEquivalences C).id_mem X) =
      Iso.refl (((weakEquivalences C).Q).obj X) :=
  weakEquivalenceIso_id X

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : weakEquivalences C f) (hg : weakEquivalences C g) :
    weakEquivalenceIso (f ≫ g)
        ((weakEquivalences C).comp_mem f g hf hg) =
      (weakEquivalenceIso f hf).trans (weakEquivalenceIso g hg) :=
  weakEquivalenceIso_comp f g hf hg

example {X Y : C} (f : X ⟶ Y)
    (hf hf' : weakEquivalences C f) :
    weakEquivalenceIso f hf = weakEquivalenceIso f hf' := by
  congr

#check HomotopicalAlgebra.weakEquivalenceIso.{0, 0}
#check HomotopicalAlgebra.weakEquivalenceIso.{1, 1}
#check HomotopicalAlgebra.weakEquivalenceIso.{0, 1}
#check HomotopicalAlgebra.weakEquivalenceIso.{1, 0}

example : True := by
  fail_if_success exact HomotopicalAlgebra.weakEquivalenceIso_hom
  fail_if_success exact HomotopicalAlgebra.weakEquivalenceIso_inv
  trivial

#print axioms HomotopicalAlgebra.weakEquivalenceIso
#print axioms HomotopicalAlgebra.weakEquivalenceIso_id
#print axioms HomotopicalAlgebra.weakEquivalenceIso_comp
