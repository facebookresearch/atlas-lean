/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorCoherence

/-!
# The closed structure of the actual chosen derived tensor

Each right adjoint is the previously constructed original `Hom(QX, R-)`
functor. Its adjunction is the complete chosen tensor–Hom adjunction, including
the same original Hom functions, units, counits and triangles. The full
parametrized naturality is retained by the same derived bifunctor.

Source: Hovey, *Model Categories*, Proposition 4.3.1 and Theorem 4.3.2.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorConstructions.MonoidalHo

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

/-- The produced monoidal structure has the exact original derived left tensor functor. -/
theorem tensorLeft_eq (X : MonoidalHo d) : tensorLeft X = (tensor d).obj X := rfl

/-- The actual original Q/R adjunction constructs closedness at every homotopy object. -/
@[instance_reducible]
def closed (X : MonoidalHo d) : Closed X where
  rightAdj := (derivedInternalHom d).obj (op X)
  adj := by
    change (tensor d).obj X ⊣ (derivedInternalHom d).obj (op X)
    exact DerivedTensorAdjunction.adjunction d X

/-- The whole chosen homotopy category is closed with the actual tensor–Hom adjunction. -/
instance monoidalClosed : MonoidalClosed (MonoidalHo d) where
  closed := closed d

/-- Every produced right adjoint is the same complete original derived internal-Hom functor. -/
theorem ihom_eq (X : MonoidalHo d) : ihom X = (derivedInternalHom d).obj (op X) := rfl

/-- The closed adjunction retains the exact constructed tensor–Hom adjunction record. -/
theorem ihom_adjunction_eq (X : MonoidalHo d) :
    ihom.adjunction X = DerivedTensorAdjunction.adjunction d X := rfl

/-- Currying keeps the same actual full derived Hom function. -/
theorem curry_eq (X Y Z : MonoidalHo d) (f : X ⊗ Y ⟶ Z) :
    MonoidalClosed.curry f = DerivedTensorAdjunction.homEquiv d X Y Z f := by
  change (DerivedTensorAdjunction.adjunction d X).homEquiv Y Z f = _
  exact DerivedTensorAdjunction.adjunction_homEquiv d X Y Z f

/-- Every target morphism uses the original derived internal-Hom morphism function. -/
theorem ihom_map_eq (X : MonoidalHo d) {Y Z : MonoidalHo d} (f : Y ⟶ Z) :
    (ihom X).map f = ((derivedInternalHom d).obj (op X)).map f := rfl

/-- Precomposition in the produced closed structure is the same actual first-variable
derived Hom map, as forced by the complete original parametrized adjunction. -/
theorem ihom_pre_eq {X Y : MonoidalHo d} (f : X ⟶ Y) :
    MonoidalClosed.pre f = (derivedInternalHom d).map f.op := by
  apply NatTrans.ext
  funext Z
  let B := ((derivedInternalHom d).obj (op Y)).obj Z
  have hpre := MonoidalClosed.curry_uncurry ((MonoidalClosed.pre f).app Z)
  rw [MonoidalClosed.uncurry_pre, curry_eq] at hpre
  have h := DerivedTensorAdjunction.homEquiv_naturality_parameter d f B Z
    ((DerivedTensorAdjunction.adjunction d Y).counit.app Z)
  have hc : DerivedTensorAdjunction.homEquiv d Y B Z
      ((DerivedTensorAdjunction.adjunction d Y).counit.app Z) = 𝟙 B := by
    rw [← DerivedTensorAdjunction.adjunction_homEquiv]
    rw [← (DerivedTensorAdjunction.adjunction d Y).homEquiv_symm_id Z, Equiv.apply_symm_apply]
  rw [hc, Category.id_comp] at h
  exact hpre.symm.trans h

/-- Every contravariant source arrow in the closed internal-Hom bifunctor retains its
original complete derived internal-Hom arrow. -/
theorem internalHom_map_eq {X Y : (MonoidalHo d)ᵒᵖ} (f : X ⟶ Y) :
    (MonoidalClosed.internalHom (C := MonoidalHo d)).map f = (derivedInternalHom d).map f :=
  ihom_pre_eq d f.unop

end HomotopicalAlgebra.DerivedTensorConstructions.MonoidalHo
