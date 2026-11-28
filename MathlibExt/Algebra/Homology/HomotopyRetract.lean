/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Homotopy

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe v u

namespace HomotopyEquiv

variable {V : Type u} [Category.{v} V] [Preadditive V]
  {ι : Type*} {c : ComplexShape ι}
  {C D : HomologicalComplex V c}

/-- Let `V` be preadditive and `C,D` complexes of any shape.
For maps `f : C → D`, `g : D → C` with `f ≫ g=𝟙 C` and a
chain homotopy `g ≫ f ≃ 𝟙 D`, the two maps form a homotopy
equivalence `C ≃ D`. -/
def ofRetract (hom : C ⟶ D) (inv : D ⟶ C)
    (hom_inv_id : hom ≫ inv = 𝟙 C)
    (homotopy_inv_hom_id : Homotopy (inv ≫ hom) (𝟙 D)) :
    HomotopyEquiv C D where
  hom := hom
  inv := inv
  homotopyHomInvId := Homotopy.ofEq hom_inv_id
  homotopyInvHomId := homotopy_inv_hom_id

@[simp]
theorem ofRetract_hom (hom : C ⟶ D) (inv : D ⟶ C)
    (hom_inv_id : hom ≫ inv = 𝟙 C)
    (homotopy_inv_hom_id : Homotopy (inv ≫ hom) (𝟙 D)) :
    (ofRetract hom inv hom_inv_id homotopy_inv_hom_id).hom = hom := rfl

@[simp]
theorem ofRetract_inv (hom : C ⟶ D) (inv : D ⟶ C)
    (hom_inv_id : hom ≫ inv = 𝟙 C)
    (homotopy_inv_hom_id : Homotopy (inv ≫ hom) (𝟙 D)) :
    (ofRetract hom inv hom_inv_id homotopy_inv_hom_id).inv = inv := rfl

end HomotopyEquiv
