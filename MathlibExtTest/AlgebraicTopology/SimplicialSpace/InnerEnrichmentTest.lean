/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment

/-! # Public consumers of the designated inner enrichment -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace.InnerTest

/-- The actual inner vertex correspondence recovers the original map. -/
theorem hom_roundtrip {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    (innerHomEquiv X Y).symm (innerHomEquiv X Y f) = f :=
  (innerHomEquiv X Y).symm_apply_apply f

/-- Arbitrary ordinary composition is represented by actual enriched composition. -/
theorem composition {X Y Z : SimplicialSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv SSet.{u} (f ≫ g) =
      (λ_ _).inv ≫ (eHomEquiv SSet.{u} f ⊗ₘ eHomEquiv SSet.{u} g) ≫
        eComp SSet.{u} X Y Z := innerHom_comp f g

/-- The whole end retains its outer naturality equation. -/
theorem end_naturality (X Y : SimplicialSpace.{u}) {m n : SimplexCategoryᵒᵖ}
    (a : m ⟶ n) :
    innerHomπ X Y m ≫ (ihom (X.diagram.obj m)).map (Y.diagram.map a) =
      innerHomπ X Y n ≫ (pre (X.diagram.map a)).app (Y.diagram.obj n) :=
  innerHomπ_naturality X Y a

/-- The scalar acts on the inner coordinate, not the outer one. -/
theorem tensor_bidegree (K : SSet.{u}) (X : SimplicialSpace.{u})
    (m n : SimplexCategoryᵒᵖ) :
    (((innerTensor K).obj X).diagram.obj m).obj n =
      ((X.diagram.obj m).obj n × K.obj n) := innerTensor_obj_obj K X m n

/-- The all-scalar representation has both actual inverse equations. -/
theorem tensor_end_roundtrip (K : SSet.{u}) (X Y : SimplicialSpace.{u})
    (f : (innerTensor K).obj X ⟶ Y) (g : K ⟶ (X ⟶[SSet.{u}] Y)) :
    (innerTensorHomEquiv K X Y).symm (innerTensorHomEquiv K X Y f) = f ∧
      innerTensorHomEquiv K X Y ((innerTensorHomEquiv K X Y).symm g) = g :=
  ⟨(innerTensorHomEquiv K X Y).symm_apply_apply f,
    (innerTensorHomEquiv K X Y).apply_symm_apply g⟩

/-- Both tensor/cotensor triangles concern the original designated maps. -/
theorem tensor_cotensor_triangles (K : SSet.{u}) (X : SimplicialSpace.{u}) :
    (innerTensor K).map ((innerTensorCotensorAdjunction K).unit.app X) ≫
      (innerTensorCotensorAdjunction K).counit.app ((innerTensor K).obj X) =
        𝟙 ((innerTensor K).obj X) ∧
    (innerTensorCotensorAdjunction K).unit.app ((innerCotensor K).obj X) ≫
      (innerCotensor K).map ((innerTensorCotensorAdjunction K).counit.app X) =
        𝟙 ((innerCotensor K).obj X) :=
  ⟨innerTensorCotensor_left_triangle K X, innerTensorCotensor_right_triangle K X⟩

/-- Future lifting APIs consume the genuine native parametrized adjunction. -/
example : innerTensorBifunctor.{u} ⊣₂ innerHomFunctor.{u} := innerTensorHomAdjunction₂

end SimplicialSpace.InnerTest
