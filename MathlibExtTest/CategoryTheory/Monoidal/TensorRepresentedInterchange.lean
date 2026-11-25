/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

module

public import MathlibExt.CategoryTheory.Monoidal.TensorRepresentedInterchange
public import Mathlib.Tactic.Linter.Lint

/-! # Public use of interchange in an arbitrary monoidal category -/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.TensorRepresentedInterchange
open scoped MonoidalCategory

namespace CategoryTheory.TensorRepresentedInterchangeTests

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Every represented endofunctor commutes with a fixed right tensor as a whole functor. -/
def compareWithRightTensor (A : C) (S : C ⥤ C) (e : MonoidalCategory.tensorLeft A ≅ S) (Y : C) :
    MonoidalCategory.tensorRight Y ⋙ S ≅ S ⋙ MonoidalCategory.tensorRight Y :=
  interchangeFunctorIso A S e Y

/-- Both arbitrary factor maps and an independent target map can be transported through interchange. -/
theorem afterTargetMap (A : C) (S : C ⥤ C) (e : MonoidalCategory.tensorLeft A ≅ S)
    {X X' Y Y' Z : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : S.obj X' ⊗ Y' ⟶ Z) :
    S.map (f ⊗ₘ g) ≫ (interchange A S e X' Y').hom ≫ h =
      (interchange A S e X Y).hom ≫ (S.map f ⊗ₘ g) ≫ h :=
  interchange_naturality_assoc A S e f g h

/-- The inverse comparison transports the same complete pair of input maps. -/
theorem inverseNaturality (A : C) (S : C ⥤ C) (e : MonoidalCategory.tensorLeft A ≅ S)
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (S.map f ⊗ₘ g) ≫ (interchange A S e X' Y').inv =
      (interchange A S e X Y).inv ≫ S.map (f ⊗ₘ g) := by
  apply (cancel_mono (interchange A S e X' Y').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [interchange_naturality, Iso.inv_hom_id_assoc]

/-- The identity representation specializes interchange to the actual inverse associator. -/
theorem identityRepresentation (A X Y : C) :
    interchange A (MonoidalCategory.tensorLeft A) (Iso.refl _) X Y = (α_ A X Y).symm := by
  apply Iso.ext
  simp only [interchange_hom, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, id_whiskerRight, Iso.symm_hom]
  exact Category.comp_id _

/-- The complete functor isomorphism retains the two inverse maps at every input. -/
theorem functorComponentsInverse (A : C) (S : C ⥤ C)
    (e : MonoidalCategory.tensorLeft A ≅ S) (X Y : C) :
    (compareWithRightTensor A S e Y).hom.app X ≫ (compareWithRightTensor A S e Y).inv.app X =
      𝟙 (S.obj (X ⊗ Y)) :=
  Iso.hom_inv_id_app _ X

/-- The full representing-object and functor comparison commutes with the unchanged right factor. -/
theorem representingCoefficientNaturality {A A' : C} {S S' : C ⥤ C}
    (p : A ⟶ A') (q : S ⟶ S')
    (e : MonoidalCategory.tensorLeft A ≅ S)
    (e' : MonoidalCategory.tensorLeft A' ≅ S')
    (h : ∀ X : C, (p ▷ X) ≫ e'.hom.app X = e.hom.app X ≫ q.app X)
    (X Y : C) :
    q.app (X ⊗ Y) ≫ (interchange A' S' e' X Y).hom =
      (interchange A S e X Y).hom ≫ (q.app X ▷ Y) :=
  coefficient_naturality p q e e' h X Y

#print axioms coefficient_naturality
#print axioms representingCoefficientNaturality

#print axioms interchange
#print axioms interchange_hom
#print axioms interchange_naturality
#print axioms interchange_naturality_assoc
#print axioms interchangeFunctorIso
#print axioms compareWithRightTensor
#print axioms afterTargetMap
#print axioms inverseNaturality
#print axioms identityRepresentation
#print axioms functorComponentsInverse

#lint only unusedArguments in MathlibExt.CategoryTheory.Monoidal.TensorRepresentedInterchange
#lint only unusedArguments in MathlibExtTest.CategoryTheory.Monoidal.TensorRepresentedInterchange

end CategoryTheory.TensorRepresentedInterchangeTests
