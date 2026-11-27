/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOneParityNaturality

/-!
# Naturality clients for even-odd coordinates

These clients use maps of inverse sequences to compare the even and odd
product factors and the natural odd-sign automorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCountableProducts C] [HasBinaryBiproducts C]
  {A B D : ℕᵒᵖ ⥤ C} (α : A ⟶ B) (β : B ⟶ D)

example (m : ℕ) :
    parityEvenProductMap α ≫ Pi.π (parityEvenFamily B) m =
      Pi.π (parityEvenFamily A) m ≫ α.app (op (2 * m)) :=
  parityEvenProductMap_π α m

example (m : ℕ) :
    parityOddProductMap α ≫ Pi.π (parityOddFamily B) m =
      Pi.π (parityOddFamily A) m ≫ α.app (op (2 * m + 1)) :=
  parityOddProductMap_π α m

example :
    parityProductMap α ≫ (parityProductIso B).hom =
      (parityProductIso A).hom ≫ sequentialProductMap α :=
  parityProductIso_naturality α

example :
    parityProductMap α ≫ (paritySignIso B).hom =
      (paritySignIso A).hom ≫ sequentialProductMap α :=
  paritySignIso_naturality α

example :
    sequentialProductMap α ≫ (paritySignedSequentialProductIso B).hom =
      (paritySignedSequentialProductIso A).hom ≫ sequentialProductMap α :=
  paritySignedSequentialProductIso_naturality α

example :
    sequentialProductMap α ≫ (paritySignedSequentialProductIso B).inv =
      (paritySignedSequentialProductIso A).inv ≫ sequentialProductMap α :=
  paritySignedSequentialProductIso_inv_naturality α

example : parityProductMap (𝟙 A) = 𝟙 (parityProduct A) :=
  parityProductMap_id A

example : parityProductMap α ≫ parityProductMap β =
    parityProductMap (α ≫ β) :=
  parityProductMap_comp α β

end CategoryTheory.Limits

end

#print axioms CategoryTheory.Limits.parityProductIso_naturality
#print axioms CategoryTheory.Limits.paritySignIso_naturality
#print axioms CategoryTheory.Limits.paritySignedSequentialProductIso_naturality
