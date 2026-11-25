/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Adjunction.OriginalParametrizedPostcomposition

/-!
# Proper whole original parameterized postcomposition clients

Both complete original adjunctions and the actual scalar maps remain
quantified in the original postcomposed Hom naturality statement.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Functor

namespace OriginalParametrizedPostcompositionClients

variable {S : Type u₁} {C : Type u₂} {D : Type u₃} {E : Type u₄}
variable [Category.{v₁} S] [Category.{v₂} C] [Category.{v₃} D] [Category.{v₄} E]
variable {F : S ⥤ C ⥤ D} {G : Sᵒᵖ ⥤ D ⥤ C} {L : D ⥤ E} {R : E ⥤ D}
variable (adj₂ : F ⊣₂ G) (adj : L ⊣ R)

open ParametrizedAdjunction.OriginalPostcomposition

/-- The whole original postcomposed scalar map retains the same complete original adjoint Hom bijections. -/
theorem whole_original_scalar_map {K M : S} (i : K ⟶ M) {A : C} {B : E}
    (f : ((left (F := F) (L := L)).obj M).obj A ⟶ B) :
    ((adjunction adj₂ adj).adj K).homEquiv A B (((left (F := F) (L := L)).map i).app A ≫ f) =
      ((adjunction adj₂ adj).adj M).homEquiv A B f ≫ ((right (G := G) (R := R)).map i.op).app B :=
  (adjunction adj₂ adj).homEquiv_naturality_one i f

end OriginalParametrizedPostcompositionClients
