/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategoryFunctoriality
import Mathlib.CategoryTheory.Comma.Over.Basic
import MathlibExt.CategoryTheory.Comma.UnderPostEquality

/-!
# The actual canonical scalar undercategory diagram of an original object

At each original scalar degree use the native undercategory of the SAME
canonical ScalarObject. Every ordinal operator is the native Under.post
of the SAME original scalarOperator. All original objects, complete
arrows, triangles and forgetful maps are retained. This is the actual
one-sided enriched nerve input; no fibre or weak outcome is assumed.
-/

noncomputable section
universe u v
open CategoryTheory Opposite

namespace SSet.ScalarUnderCategory

variable (C : Type v) [EnrichedCategory SSet.{u} C] (z : C)

/-- The SAME canonical original source object in the specified scalar degree. -/
abbrev sourceObject (q : SimplexCategoryᵒᵖ) : ScalarObject C q := ⟨z⟩

/-- The actual native undercategory retains every full original arrow from the same original source. -/
abbrev category (q : SimplexCategoryᵒᵖ) := Under (sourceObject C z q)

/-- The SAME full original scalar operator acts on each actual original undercategory arrow and triangle. -/
def operator {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) : category C z q ⥤ category C z r :=
  Under.post (X := sourceObject C z q) (scalarOperator (C := C) f)

/-- The actual native forgetful functor keeps the SAME original canonical target and whole arrow. -/
abbrev forget (q : SimplexCategoryᵒᵖ) : category C z q ⥤ ScalarObject C q :=
  Under.forget (sourceObject C z q)

/-- Every SAME whole original scalar under operator retains its exact native forgetful square. -/
theorem operator_forget {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    operator C z f ⋙ forget C z r = forget C z q ⋙ scalarOperator (C := C) f := rfl

/-- Native scalar undercategory operators preserve the SAME whole original identity functor. -/
theorem operator_id (q : SimplexCategoryᵒᵖ) : operator C z (𝟙 q) = 𝟭 (category C z q) := by
  exact eq_of_heq (Under.post_hcongr (X := sourceObject C z q) (scalarOperator_id (C := C) q))

/-- Every SAME original composite scalar undercategory operator is the actual full native composite functor. -/
theorem operator_comp {q r s : SimplexCategoryᵒᵖ} (f : q ⟶ r) (g : r ⟶ s) :
    operator C z (f ≫ g) = operator C z f ⋙ operator C z g := by
  exact eq_of_heq (Under.post_hcongr (X := sourceObject C z q) (scalarOperator_comp (C := C) f g))

/-- The SAME actual original scalar undercategory diagram, retaining independent object and Hom universes. -/
def diagram : SimplexCategoryᵒᵖ ⥤ Cat.{u, max u v} where
  obj q := Cat.of (category C z q)
  map f := (operator C z f).toCatHom
  map_id q := by apply Cat.ext; exact operator_id C z q
  map_comp f g := by apply Cat.ext; exact operator_comp C z f g

end SSet.ScalarUnderCategory
