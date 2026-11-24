/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Whole original adjunction parameter restriction

Every original map of a genuine parameter functor retains the same full
parameterized adjunction. This restricts only the parameter category and
does not alter any ordinary Hom or coefficient map.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃
open CategoryTheory Opposite

namespace CategoryTheory.ParametrizedAdjunction.OriginalParameter

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
variable [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
variable {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire actual parameter functor retains all native component adjunctions and
opposite parameter maps. -/
def adjunction (adj₂ : F ⊣₂ G) (T : C₀ ⥤ C₁) : T ⋙ F ⊣₂ T.op ⋙ G :=
  ParametrizedAdjunction.mk' (fun A => adj₂.adj (T.obj A))
    (fun {A B} p {X Y} f => adj₂.homEquiv_naturality_one
      (X₁ := T.obj A) (Y₁ := T.obj B) (X₂ := X) (X₃ := Y) (T.map p) f)

/-- Every native parameter component is exactly its actual original image component adjunction. -/
theorem adjunction_adj (adj₂ : F ⊣₂ G) (T : C₀ ⥤ C₁) (A : C₀) :
    (adjunction adj₂ T).adj A = adj₂.adj (T.obj A) := rfl

end CategoryTheory.ParametrizedAdjunction.OriginalParameter
