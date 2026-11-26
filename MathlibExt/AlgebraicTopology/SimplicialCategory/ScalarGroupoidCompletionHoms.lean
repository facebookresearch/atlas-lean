/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategoryFunctoriality
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# Native completion Homs of the canonical scalar categories

The canonical ScalarObject category at every degree is completed
by Mathlib's native FreeGroupoid. Its complete Hom maps use the same
canonical scalarOperator and every ordinal operator.
The object images retain their literal scalar labels. No
completion weakness or model/derived comparison result is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion

variable (C : Carrier.{u})

/-- The native groupoid completion of the canonical scalar category. -/
abbrev category (q : SimplexCategoryᵒᵖ) := FreeGroupoid (SSet.ScalarObject C q)

/-- The same object has its native completion image at the scalar
degree. -/
abbrev vertex (q : SimplexCategoryᵒᵖ) (x : C) : category C q :=
  FreeGroupoid.mk (SSet.ScalarObject.mk (Δ := q) x)

/-- Every full native Hom of the same canonical degreewise completion, at its endpoints. -/
abbrev Hom (q : SimplexCategoryᵒᵖ) (x y : C) : Type u := vertex C q x ⟶ vertex C q y

/-- Each same canonical scalar operator induces the native completion
functor. -/
def operator {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) : category C q ⥤ category C r :=
  FreeGroupoid.map (SSet.scalarOperator (C := C) f)

/-- The native completion operator keeps exactly the same object at the new
scalar degree. -/
theorem operator_vertex {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) (x : C) :
    (operator C f).obj (vertex C q x) = vertex C r x := rfl

/-- The same canonical scalar identity completes to the native identity functor. -/
theorem operator_id (q : SimplexCategoryᵒᵖ) : operator C (𝟙 q) = 𝟭 (category C q) := by
  unfold operator
  rw [SSet.scalarOperator_id]
  exact FreeGroupoid.map_id _

/-- Native completion retains the same full canonical composite operator. -/
theorem operator_comp {q r s : SimplexCategoryᵒᵖ} (f : q ⟶ r) (g : r ⟶ s) :
    operator C (f ≫ g) = operator C f ⋙ operator C g := by
  unfold operator
  rw [SSet.scalarOperator_comp]
  exact FreeGroupoid.map_comp _ _

/-- The native operator acts on every same full completed Hom simplex. -/
def mapHom {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) {x y : C} (a : Hom C q x y) : Hom C r x y :=
  (operator C f).map a

/-- The same identity operator fixes every full completed Hom simplex. -/
theorem mapHom_id (q : SimplexCategoryᵒᵖ) (x y : C) (a : Hom C q x y) : mapHom C (𝟙 q) a = a :=
  eq_of_heq (Functor.hcongr_hom (operator_id C q) a)

/-- Every complete completed Hom simplex retains the same operator composition law. -/
theorem mapHom_comp {q r s : SimplexCategoryᵒᵖ} (f : q ⟶ r) (g : r ⟶ s)
    {x y : C} (a : Hom C q x y) : mapHom C (f ≫ g) a = mapHom C g (mapHom C f a) :=
  eq_of_heq (Functor.hcongr_hom (operator_comp C f g) a)

/-- The same native completed Hom is a full simplicial set using every 
canonical operator. -/
def hom (x y : C) : SSet.{u} where
  obj q := Hom C q x y
  map f := ↾fun a => mapHom C f a
  map_id q := by ext a; exact mapHom_id C q x y a
  map_comp f g := by ext a; exact mapHom_comp C f g a

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
