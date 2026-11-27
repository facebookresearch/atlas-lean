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
# Native completion Homs of the canonical original scalar categories

The canonical ScalarObject category at every original degree is completed
by Mathlib's native FreeGroupoid. Its complete Hom maps use the SAME
canonical scalarOperator and every actual original ordinal operator.
The original object images retain their literal scalar labels. No
completion weakness or model/derived comparison result is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion

variable (C : Carrier.{u})

/-- The actual native groupoid completion of the canonical original scalar category. -/
abbrev category (q : SimplexCategoryᵒᵖ) := FreeGroupoid (SSet.ScalarObject C q)

/-- The SAME original object has its actual native completion image at the original scalar
degree. -/
abbrev vertex (q : SimplexCategoryᵒᵖ) (x : C) : category C q :=
  FreeGroupoid.mk (SSet.ScalarObject.mk (Δ := q) x)

/-- Every full native Hom of the SAME canonical degreewise completion, at its original endpoints. -/
abbrev Hom (q : SimplexCategoryᵒᵖ) (x y : C) : Type u := vertex C q x ⟶ vertex C q y

/-- Each SAME canonical original scalar operator induces the actual whole native completion
functor. -/
def operator {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) : category C q ⥤ category C r :=
  FreeGroupoid.map (SSet.scalarOperator (C := C) f)

/-- The native completion operator keeps exactly the SAME original object at the new
original scalar degree. -/
theorem operator_vertex {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) (x : C) :
    (operator C f).obj (vertex C q x) = vertex C r x := rfl

/-- The SAME entire canonical scalar identity completes to the actual native identity functor. -/
theorem operator_id (q : SimplexCategoryᵒᵖ) : operator C (𝟙 q) = 𝟭 (category C q) := by
  unfold operator
  rw [SSet.scalarOperator_id]
  exact FreeGroupoid.map_id _

/-- Native completion retains the SAME full canonical original composite operator. -/
theorem operator_comp {q r s : SimplexCategoryᵒᵖ} (f : q ⟶ r) (g : r ⟶ s) :
    operator C (f ≫ g) = operator C f ⋙ operator C g := by
  unfold operator
  rw [SSet.scalarOperator_comp]
  exact FreeGroupoid.map_comp _ _

/-- The actual native operator acts on every SAME full original completed Hom simplex. -/
def mapHom {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) {x y : C} (a : Hom C q x y) : Hom C r x y :=
  (operator C f).map a

/-- The SAME identity operator fixes every full original completed Hom simplex. -/
theorem mapHom_id (q : SimplexCategoryᵒᵖ) (x y : C) (a : Hom C q x y) : mapHom C (𝟙 q) a = a :=
  eq_of_heq (Functor.hcongr_hom (operator_id C q) a)

/-- Every complete original completed Hom simplex retains the SAME operator composition law. -/
theorem mapHom_comp {q r s : SimplexCategoryᵒᵖ} (f : q ⟶ r) (g : r ⟶ s)
    {x y : C} (a : Hom C q x y) : mapHom C (f ≫ g) a = mapHom C g (mapHom C f a) :=
  eq_of_heq (Functor.hcongr_hom (operator_comp C f g) a)

/-- The SAME native completed Hom is a genuine full simplicial set using every original
canonical operator. -/
def hom (x y : C) : SSet.{u} where
  obj q := Hom C q x y
  map f := ↾fun a => mapHom C f a
  map_id q := by ext a; exact mapHom_id C q x y a
  map_comp f g := by ext a; exact mapHom_comp C f g a

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
